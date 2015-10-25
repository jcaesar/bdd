theory AbstractBDD
imports BoolFunc
begin

datatype nodelabel = LabeledNode nat | DTrue | DFalse 
record abdd_node =
	var :: nat
	label :: nodelabel
	right :: nodelabel
	left :: nodelabel
	
record abdd =
	nodes :: "abdd_node list"
	start :: nodelabel

definition abdd_reference_integrity_set :: "abdd \<Rightarrow> bool" where
"abdd_reference_integrity_set b \<equiv> (\<forall>n \<in> set (nodes b).
	(\<forall>m \<in> set (nodes b). (label m = label n) \<longrightarrow> (m = n)) \<and> (
	case (label n) of 
		LabeledNode _ \<Rightarrow> ((\<exists>l \<in> set (nodes b). label l = left n) \<and> (\<exists>l \<in> set (nodes b). label l = right n)) |
		_ \<Rightarrow> True))"

definition "abdd_collect_refs bdd = start bdd # map right (nodes bdd) @ map left (nodes bdd)"
definition abdd_reference_integrity :: "abdd \<Rightarrow> bool" where
	"abdd_reference_integrity bdd \<equiv> (\<forall>lb \<in> set (abdd_collect_refs bdd). \<exists>node \<in> set (nodes bdd). label node = lb)"
definition abdd_nodes_unique :: "abdd \<Rightarrow> bool" where
	"abdd_nodes_unique bdd \<equiv> (\<forall>n \<in> set (nodes bdd). (\<forall>m \<in> set (nodes bdd). (label m = label n) \<longrightarrow> (m = n)))"

definition "getnode bdd lbl = List.find (\<lambda>n. label n = lbl) (nodes bdd)"

lemma getnode_noNone: "lbl \<in> set (abdd_collect_refs bdd) \<Longrightarrow> abdd_reference_integrity bdd \<Longrightarrow> getnode bdd lbl \<noteq> None"
	unfolding abdd_reference_integrity_def getnode_def
	unfolding find_None_iff
	by blast
	
lemma node_gettable:
	assumes "node \<in> set (nodes bdd)" and "abdd_reference_integrity bdd"
	shows "getnode bdd (right node) \<noteq> None" "getnode bdd (left node) \<noteq> None"
proof -
	have "(right node) \<in> set (abdd_collect_refs bdd)" "(left node) \<in> set (abdd_collect_refs bdd)"
		using assms unfolding abdd_reference_integrity_def abdd_collect_refs_def by auto
	with getnode_noNone assms(2) show "getnode bdd (right node) \<noteq> None" "getnode bdd (left node) \<noteq> None" by simp_all
qed
lemma getnode_label_inv:
	assumes "node \<in> set (nodes bdd)" and "abdd_reference_integrity bdd"
	shows "label (the (getnode bdd (right node))) = right node" "label (the (getnode bdd (left node))) = left node"
using node_gettable[OF assms] by simp_all (metis (mono_tags, lifting) find_Some_iff option.sel getnode_def)+
lemma getnode_in:
	assumes "node \<in> set (nodes bdd)" and "abdd_reference_integrity bdd"
	shows "the (getnode bdd (right node)) \<in> set (nodes bdd)" "the (getnode bdd (left node)) \<in> set (nodes bdd)"
using node_gettable[OF assms] by simp_all (metis find_Some_iff getnode_def nth_mem option.sel)+
lemma getnode_in2: "getnode bdd (LabeledNode ln) = Some x \<Longrightarrow> x \<in> set (nodes bdd)"
	unfolding getnode_def find_Some_iff by force

definition "abdd_is_child c n \<equiv> (label c = left n \<or> label c = right n)"
inductive abdd_reachable :: "abdd \<Rightarrow> abdd_node \<Rightarrow> abdd_node \<Rightarrow> bool" where
ar_base: "ln2 \<in> set (nodes bdd) \<Longrightarrow> abdd_is_child ln2 ln  \<Longrightarrow> abdd_reachable bdd ln ln2" |
ar_step: "ln3 \<in> set (nodes bdd) \<Longrightarrow> abdd_reachable bdd ln ln2 \<Longrightarrow> abdd_is_child ln3 ln2  \<Longrightarrow> abdd_reachable bdd ln ln3"
code_pred abdd_reachable .
definition "abdd_reachable_set bdd node = {n |n. abdd_reachable bdd node n}"
definition "abdd_cycle_free bdd = (\<forall>node \<in> set (nodes bdd). \<not> abdd_reachable bdd node node)"

lemma reachable_trans: "abdd_reachable bdd b c \<Longrightarrow> abdd_reachable bdd a b \<Longrightarrow> abdd_reachable bdd a c"
	apply(induction rule: abdd_reachable.induct)
	 apply(metis ar_step)+
done
lemma reachable_child: 
	assumes "node \<in> set (nodes bdd)" "abdd_reference_integrity bdd"
	shows "abdd_reachable bdd node (the (getnode bdd (right node)))" "abdd_reachable bdd node (the (getnode bdd (left node)))"
proof -
	have ic: "abdd_is_child (the (getnode bdd (right node))) node" "abdd_is_child (the (getnode bdd (left node))) node"
		unfolding abdd_is_child_def using node_gettable[OF assms] getnode_label_inv[OF assms] by simp_all 
	show "abdd_reachable bdd node (the (getnode bdd (right node)))" "abdd_reachable bdd node (the (getnode bdd (left node)))" using getnode_in[OF assms] ic ar_base by simp_all
qed
lemma step_reachable_subset_r: "node \<in> set (nodes bdd) \<Longrightarrow> abdd_reference_integrity bdd \<Longrightarrow> 
       abdd_reachable_set bdd (the (getnode bdd (right node))) \<subseteq> (abdd_reachable_set bdd node)"
proof(rule, unfold abdd_reachable_set_def, simp, fast elim: reachable_trans[OF _ reachable_child(1)]) qed
lemma step_reachable_subset_l: "node \<in> set (nodes bdd) \<Longrightarrow> abdd_reference_integrity bdd \<Longrightarrow> 
       abdd_reachable_set bdd (the (getnode bdd (left node))) \<subseteq> (abdd_reachable_set bdd node)"
proof(rule, unfold abdd_reachable_set_def, simp, fast elim: reachable_trans[OF _ reachable_child(2)]) qed

lemma hlp1: "x \<in> {n |n. P n} \<Longrightarrow> P x" by blast
lemma notselfreach:
	assumes "abdd_cycle_free bdd"
	shows "node \<in> abdd_reachable_set bdd node \<Longrightarrow> False"
proof(unfold abdd_reachable_set_def, drule hlp1)
	case goal1
	then have "node \<in> set (nodes bdd)" by(cases rule: abdd_reachable.cases) simp_all
	moreover note assms[unfolded abdd_cycle_free_def]
	ultimately show False using goal1 by simp
qed
lemma step_reachable_rsubset_l:
	assumes a1: "abdd_cycle_free bdd"
	assumes a2: "node \<in> set (nodes bdd)" "abdd_reference_integrity bdd"
	shows "abdd_reachable_set bdd (the (getnode bdd (left node))) \<subset> (abdd_reachable_set bdd node)"
	apply rule
	 using step_reachable_subset_l[OF a2] apply simp
	using notselfreach[OF a1] unfolding abdd_reachable_set_def using a2 mem_Collect_eq reachable_child(2) apply auto
done
lemma step_reachable_rsubset_r:
	assumes a1: "abdd_cycle_free bdd"
	assumes a2: "node \<in> set (nodes bdd)" "abdd_reference_integrity bdd"
	shows "abdd_reachable_set bdd (the (getnode bdd (right node))) \<subset> (abdd_reachable_set bdd node)"
	apply rule
	 using step_reachable_subset_r[OF a2] apply simp
	using notselfreach[OF a1] unfolding abdd_reachable_set_def using a2 mem_Collect_eq reachable_child(1) apply auto
done

lemma abdd_reachable_subset: "abdd_reachable_set bdd node \<subseteq> set (nodes bdd)"
	apply(unfold abdd_reachable_set_def)
	apply rule
	apply(drule hlp1)
	using abdd_reachable.simps apply blast
done
lemma abdd_reachable_fin: "finite (abdd_reachable_set bdd node)"
	apply(rule finite_subset)
	 apply(rule abdd_reachable_subset)
	apply(rule finite_set)
done

lemma abdd_reachable_in_reachable:
	"abdd_reachable bdd n1 n2 \<Longrightarrow> n2 \<in> abdd_reachable_set bdd n1"
	unfolding abdd_reachable_set_def by simp

definition "abdd_terminal state = (case state of LabeledNode _ \<Rightarrow> False | _ \<Rightarrow> True)" 

inductive abdd_smallstep  where
start: "abdd_smallstep bdd assignment (start bdd)" |
step[elim]: "abdd_smallstep bdd assignment state \<Longrightarrow> \<not> abdd_terminal state \<Longrightarrow> node \<in> set (nodes bdd) \<Longrightarrow> label node = state \<Longrightarrow> abdd_smallstep bdd assignment ((if assignment ! var node then right else left) node)"
print_theorems
code_pred abdd_smallstep .
inductive abdd_smallstep2  where
start: "abdd_smallstep2 bdd assignment (start bdd)" |
stepright: "abdd_smallstep2 bdd assignment state \<Longrightarrow> \<not> abdd_terminal state \<Longrightarrow> node \<in> set (nodes bdd) \<Longrightarrow> label node = state \<Longrightarrow> assignment ! var node \<Longrightarrow> abdd_smallstep2 bdd assignment (right node)" |
stepleft: "abdd_smallstep2 bdd assignment state \<Longrightarrow> \<not> abdd_terminal state \<Longrightarrow> node \<in> set (nodes bdd) \<Longrightarrow> label node = state \<Longrightarrow> \<not>assignment ! var node \<Longrightarrow> abdd_smallstep2 bdd assignment (left node)"
lemma abdd_smallstep_2_eq: "abdd_smallstep bdd ass state = abdd_smallstep2 bdd ass state"
	apply(rule)
	 apply(induction rule: abdd_smallstep.induct)
	  apply(simp add: abdd_smallstep2.start)
	 apply(force dest: abdd_smallstep2.stepright abdd_smallstep2.stepleft)
	apply(induction rule: abdd_smallstep2.induct)
	  apply(simp add: abdd_smallstep.start)
	 apply(force dest: abdd_smallstep.step)
	apply(force dest: abdd_smallstep.step)
done

definition "abdd_xor \<equiv> \<lparr> nodes = [
	\<lparr> var = 0, label = LabeledNode 5, right = LabeledNode 4 , left = LabeledNode 3 \<rparr>,
	\<lparr> var = 1, label = LabeledNode 4, right = DFalse , left = DTrue \<rparr>,
	\<lparr> var = 1, label = LabeledNode 3, right = DTrue , left = DFalse \<rparr>,
	\<lparr> var = 0, label = DTrue , right = DTrue , left = DTrue \<rparr>,
	\<lparr> var = 0, label = DFalse , right = DFalse , left = DFalse \<rparr>
], start = LabeledNode 5\<rparr>"

lemma "abdd_reference_integrity abdd_xor = True" by eval
lemma[code]: "abdd_cycle_free abdd_xor = True" 
unfolding abdd_cycle_free_def eq_True apply(subst abdd_xor_def, simp) apply(rule) oops
lemma "abdd_smallstep abdd_xor [False, True] DTrue" 
proof -
	have 1: "abdd_smallstep abdd_xor [False, True] (start abdd_xor)" by(simp add: abdd_smallstep.start)
	have 2: "\<lparr> var = 0, label = LabeledNode 5, right = LabeledNode 4 , left = LabeledNode 3 \<rparr> \<in> set (nodes abdd_xor)" by(simp add: abdd_xor_def)
	have 3: "abdd_smallstep abdd_xor [False, True] (LabeledNode 3)" using abdd_smallstep.step[OF 1 _ 2] by(simp add: abdd_xor_def abdd_terminal_def)
	have 4: "\<lparr> var = 1, label = LabeledNode 3, right = DTrue , left = DFalse \<rparr> \<in> set (nodes abdd_xor)" by(simp add: abdd_xor_def)
	show 5: "abdd_smallstep abdd_xor [False, True] DTrue" using abdd_smallstep.step[OF 3 _ 4] by(simp add: abdd_xor_def abdd_terminal_def)
qed (* So how do I do this automatically? Guess I don't *)

definition "abstract_abdd1 bdd ass = (
	if abdd_smallstep bdd ass DTrue
		then Some True else (
	if abdd_smallstep bdd ass DFalse
		then Some False
	else None))"

lemma abdd_steppable_ind: " (\<exists>node \<in> set (nodes bdd). label node = state)
	\<Longrightarrow> abdd_smallstep bdd ass state \<Longrightarrow> (\<exists>nextnode \<in> set (nodes bdd). abdd_smallstep bdd ass (label nextnode))" by blast

function abstract_abdd2 :: "abdd \<Rightarrow> nodelabel \<Rightarrow> boolfunc2" where
"abstract_abdd2 bdd DTrue = (\<lambda>as. True)" |
"abstract_abdd2 bdd DFalse = (\<lambda>as. False)" |
"abstract_abdd2 bdd (LabeledNode ln) = (if abdd_reference_integrity bdd \<and> abdd_cycle_free bdd then 
	(case getnode bdd (LabeledNode ln) of Some n \<Rightarrow> 
		(\<lambda>as. if as (var n) then abstract_abdd2 bdd (right n) as 
		else abstract_abdd2 bdd (left n) as)
		| _ \<Rightarrow> undefined) else undefined)"
by pat_completeness auto

termination abstract_abdd2
proof(relation "measure (\<lambda>(bdd, nl). case getnode bdd nl of Some n \<Rightarrow> card (abdd_reachable_set bdd n) | None \<Rightarrow> 0)", rule wf_measure)
	case goal1
	then have as: "abdd_reference_integrity bdd" "abdd_cycle_free bdd" by simp_all
	have xe: "x2 \<in> set (nodes bdd)" using getnode_in2[OF goal1(2)] . 
	have cs: "(case getnode bdd (right x2) of None \<Rightarrow> 0 | Some n \<Rightarrow> card (abdd_reachable_set bdd n)) =
		card (abdd_reachable_set bdd  (the (getnode bdd (right x2))))" using node_gettable(1)[OF xe as(1)] by force
	note psubset_card_mono[OF abdd_reachable_fin step_reachable_rsubset_r[OF as(2) xe as(1)]]
	then show ?case by(simp add: cs goal1(2))
next
	case goal2
	then have as: "abdd_reference_integrity bdd" "abdd_cycle_free bdd" by simp_all
	have xe: "x2 \<in> set (nodes bdd)" using getnode_in2[OF goal2(2)] . 
	have cs: "(case getnode bdd (left x2) of None \<Rightarrow> 0 | Some n \<Rightarrow> card (abdd_reachable_set bdd n)) =
		card (abdd_reachable_set bdd  (the (getnode bdd (left x2))))" using node_gettable(2)[OF xe as(1)] by force
	note psubset_card_mono[OF abdd_reachable_fin step_reachable_rsubset_l[OF as(2) xe as(1)]]
	then show ?case by(simp add: cs goal2(2))
qed

(* I want to try a few examples\<dots> So I need something that can execude. *)
function abdd_reachable_set_code where
"abdd_reachable_set_code bdd nods = (if abdd_reference_integrity bdd then 
	(let trunc = set (nodes bdd) \<inter> nods in (let morereach = trunc 
		\<union> (the \<circ> getnode bdd \<circ> right) ` trunc
		\<union> (the \<circ> getnode bdd \<circ> left) ` trunc in 
			(if nods \<subset> morereach 
			then abdd_reachable_set_code bdd morereach 
			else trunc)))
	else undefined)"
by pat_completeness auto
termination abdd_reachable_set_code
proof(relation "measure (\<lambda>(bdd,nods). length (nodes bdd) - card nods)", rule wf_measure, unfold comp_def)
	case goal1
	note xa = goal1(3)[unfolded goal1(2)]
	note a = goal1(4)[unfolded xa]
	have ss1: "x \<subseteq> set (nodes bdd)" unfolding goal1(2) by simp
	then have ss2: "xa \<subseteq> set (nodes bdd)" unfolding goal1(3)
		by(auto simp add: getnode_in[OF _ goal1(1)])
	have lep1: "card xa \<le> length (nodes bdd)"
		using le_trans card_mono[OF finite_set ss2, unfolded card_set] length_remdups_leq .
	have lep2: "card nods \<le> length (nodes bdd)"
		 by (meson List.finite_set card_mono finite_subset goal1(4) le_trans lep1 less_imp_le ss2)
	{ fix x y z :: nat
		have "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> x - y < x - z = (z < y)" by linarith
	} note swapdir = this
	show ?case unfolding in_measure
		by(simp add: swapdir[OF lep1 lep2] psubset_card_mono[OF _ a, simplified, unfolded xa[symmetric]])
qed
print_theorems

lemma reachable_code_subset_self: 
	"x \<subseteq> set (nodes bdd) \<Longrightarrow> abdd_reference_integrity bdd \<Longrightarrow> x \<subseteq> abdd_reachable_set_code bdd x"
proof(induction bdd x rule: abdd_reachable_set_code.induct)
	case goal1
	let ?trunc = "set (nodes bdd) \<inter> nods"
	let ?morereach = "?trunc \<union> (the \<circ> getnode bdd \<circ> right) ` ?trunc \<union> (the \<circ> getnode bdd \<circ> left) ` ?trunc"
	note mih = goal1(1)[OF goal1(3) _ _ _ _ goal1(3), of ?trunc ?morereach, OF refl refl]
	have "?morereach \<subseteq> set (nodes bdd)" using goal1(2) unfolding comp_def using getnode_in[OF _ goal1(3)] by blast
	note fih = mih[OF _ this]
	have df: "abdd_reachable_set_code bdd nods =  
		(if nods \<subset> ?morereach then abdd_reachable_set_code bdd ?morereach else ?trunc)"
		using goal1(3) by(simp add: Let_def) 
	show ?case proof(cases "nods \<subset> ?morereach")
		case False show ?thesis unfolding df[unfolded if_not_P[OF False]] using goal1(2) by simp
	next
		case True
		note fih[OF True]
		thus ?thesis using df[unfolded if_P[OF True]] using goal1(2) by blast
	qed
qed

lemma reach_eq_hlp1: "abdd_reference_integrity bdd \<Longrightarrow> ln2 \<in> abdd_reachable_set_code bdd ln \<Longrightarrow>
	abdd_is_child ln3 ln2 \<Longrightarrow> ln3 \<in> set (nodes bdd) \<Longrightarrow> ln3 \<in> abdd_reachable_set_code bdd ln"
apply(auto simp only: abdd_is_child_def)
apply(subst abdd_reachable_set_code.simps, subst abdd_reachable_set_code.simps)
sorry

lemma reach_eq_help2: "abdd_reference_integrity bdd \<Longrightarrow> \<Union>(abdd_reachable_set bdd `
         (set (nodes bdd) \<inter> nods \<union> (the \<circ> getnode bdd \<circ> right) ` (set (nodes bdd) \<inter> nods) \<union>
          (the \<circ> getnode bdd \<circ> left) ` (set (nodes bdd) \<inter> nods))) \<union>
       (set (nodes bdd) \<inter> nods \<union> (the \<circ> getnode bdd \<circ> right) ` (set (nodes bdd) \<inter> nods) \<union>
        (the \<circ> getnode bdd \<circ> left) ` (set (nodes bdd) \<inter> nods)) = 
          \<Union>(abdd_reachable_set bdd ` (set (nodes bdd) \<inter> nods)) \<union> (set (nodes bdd) \<inter> nods)"
proof
	case goal1
	have r2: "\<Union>(abdd_reachable_set bdd ` (the \<circ> getnode bdd \<circ> right) ` (set (nodes bdd) \<inter> nods))
    	\<subseteq> \<Union>(abdd_reachable_set bdd ` (set (nodes bdd) \<inter> nods))"
    	by(rule, unfold image_comp comp_def) (blast dest: step_reachable_subset_r[OF _ goal1])
    have l2: "\<Union>(abdd_reachable_set bdd ` (the \<circ> getnode bdd \<circ> left) ` (set (nodes bdd) \<inter> nods))
    	\<subseteq> \<Union>(abdd_reachable_set bdd ` (set (nodes bdd) \<inter> nods))"
    	by(rule, unfold image_comp comp_def) (blast dest: step_reachable_subset_l[OF _ goal1])
    have m: "(the \<circ> getnode bdd \<circ> right) ` (set (nodes bdd) \<inter> nods) \<union>
    	(the \<circ> getnode bdd \<circ> left) ` (set (nodes bdd) \<inter> nods) \<subseteq> \<Union>(abdd_reachable_set bdd ` (set (nodes bdd) \<inter> nods))"
    	using abdd_reachable_in_reachable reachable_child[OF _ goal1] by auto
	show ?case
		using l2 r2 m
		unfolding image_Un
		by auto
qed force

lemma subset_hlp: "({x} \<subseteq> S) = (x \<in> S)" by simp
lemma abdd_reachable_set_code_eq_hlp: "abdd_reference_integrity bdd \<Longrightarrow> node \<in> set (nodes bdd) \<Longrightarrow>
	abdd_reachable_set_code bdd {node} = abdd_reachable_set bdd node \<union> {node}"
proof
	case goal2 have "abdd_reachable_set bdd node \<subseteq> abdd_reachable_set_code bdd {node}"
		(* Caesar style proof: no facts written. *) 
		apply(rule)
		apply(unfold abdd_reachable_set_def) 
		apply(drule hlp1)
		using goal2 proof -
			case goal1 thus ?case proof(induction rule: abdd_reachable.induct)
				case goal1
				from reach_eq_hlp1[OF goal1(3) _ goal1(2) goal1(1), of "{ln}"]
					reachable_code_subset_self[of "{ln}", unfolded subset_hlp, OF goal1(4) goal1(3)]
				show ?case .
			next
				case goal2 (* with reach_eq_hlp1 show ?case by blast *)
				note mih = goal2(3)[OF goal2(5) goal2(6)]
				note reach_eq_hlp1[OF goal2(5) mih goal2(4) goal2(1)]
				thus ?case .
			qed
		qed
	then show ?case
		using reachable_code_subset_self[OF goal2(2)[unfolded subset_hlp[symmetric]] goal2(1)]
		by simp
next
	case goal1
	{ fix k e
		have "e \<in> abdd_reachable_set_code bdd k \<Longrightarrow> e \<in> \<Union>(abdd_reachable_set bdd ` k) \<union> k"
		using goal1
		proof(induction bdd k rule: abdd_reachable_set_code.induct)
			case goal1
			let ?trunc = "set (nodes bdd) \<inter> nods"
			let ?morereach = "?trunc \<union> (the \<circ> getnode bdd \<circ> right) ` ?trunc \<union> (the \<circ> getnode bdd \<circ> left) ` ?trunc"
			note mih = goal1(1)[OF goal1(3), of ?trunc ?morereach, OF refl refl _ _ goal1(3) goal1(4)]
			have df: "abdd_reachable_set_code bdd nods =  
				(if nods \<subset> ?morereach then abdd_reachable_set_code bdd ?morereach else ?trunc)"
				using goal1(3) by(simp add: Let_def) 
			thus ?case (is ?kees) 
			proof(cases "nods \<subset> ?morereach")
				case True
				note mdf = df[unfolded if_P[OF True], symmetric]
				from mih[OF True]
				show ?kees unfolding mdf unfolding reach_eq_help2[OF goal1(3)]
					using goal1(2) by blast
			next
				case False
				note mdf = df[unfolded if_not_P[OF False]]
				show ?kees using goal1(2)[unfolded mdf] by blast
			qed
		qed
			
	}
	from this[of _ "{node}"] show ?case by blast
qed

lemma [code]: "(if abdd_reference_integrity bdd \<and> abdd_cycle_free bdd then a else b) =
               (if abdd_reference_integrity bdd \<and> (\<forall>node \<in> set (nodes bdd). 
               		node \<notin> abdd_reachable_set_code bdd node) then a else b)"
using abdd_reachable_set_code_eq_hlp

lemma abdd_reachable_dub: assumes "abdd_reference_integrity bdd" "nod \<in> set (nodes bdd)"
	shows "\<Union>(abdd_reachable_set bdd ` abdd_reachable_set bdd nod) = abdd_reachable_set bdd nod"
oops
	
end

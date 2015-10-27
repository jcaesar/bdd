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
lemma getnode_in3:
	assumes "abdd_reference_integrity bdd"
	shows "the (getnode bdd (start bdd)) \<in> set (nodes bdd)"
proof -
	have 1: "start bdd \<in> set (abdd_collect_refs bdd)"
		unfolding abdd_collect_refs_def by simp 
	have "getnode bdd (start bdd) \<noteq> None"
		using getnode_noNone[OF 1 assms] .
	then show ?thesis
		by (metis find_Some_iff getnode_def nth_mem option.collapse)
qed

definition "abdd_is_child c n \<equiv> (label c = left n \<or> label c = right n)"
inductive abdd_reachable :: "abdd \<Rightarrow> abdd_node \<Rightarrow> abdd_node \<Rightarrow> bool" where
ar_base: "ln2 \<in> set (nodes bdd) \<Longrightarrow> abdd_is_child ln2 ln  \<Longrightarrow> abdd_reachable bdd ln ln2" |
ar_step: "ln3 \<in> set (nodes bdd) \<Longrightarrow> abdd_reachable bdd ln ln2 \<Longrightarrow> abdd_is_child ln3 ln2  \<Longrightarrow> abdd_reachable bdd ln ln3"
print_theorems
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
lemma hlp2: "x \<in> {n |n. P n} = P x" by blast
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
		| _ \<Rightarrow> (\<lambda>x. False)) else (\<lambda>x. False))" (* used to be undefined, but that's annoying *)
by pat_completeness auto

termination abstract_abdd2
proof(relation "measure (\<lambda>(bdd, nl). case getnode bdd nl of Some n \<Rightarrow> card (abdd_reachable_set bdd n) | None \<Rightarrow> 0)",
	rule wf_measure)
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

function abstract_abdd3 :: "abdd \<Rightarrow> boolfunc2" where
"abstract_abdd3 bdd = (if abdd_reference_integrity bdd \<and> abdd_cycle_free bdd then
	(case start bdd of 
		DTrue \<Rightarrow> (\<lambda>as. True) |
		DFalse \<Rightarrow> (\<lambda>as. False) |
		LabeledNode ln \<Rightarrow> let n = the (getnode bdd (LabeledNode ln)) in
			(\<lambda>as. if as (var n)
				then abstract_abdd3 \<lparr> nodes = nodes bdd, start = right n \<rparr> as 
				else abstract_abdd3 \<lparr> nodes = nodes bdd, start = left n \<rparr> as)
	) else (\<lambda>x. False))"
by pat_completeness auto

lemma getnode_start_inv: "getnode \<lparr> nodes = n, start = a \<rparr> l = getnode \<lparr> nodes = n, start = b \<rparr> l"
	unfolding getnode_def
	unfolding abdd.simps
	..
lemma abdd_simp_instance: "\<lparr>nodes = nodes bdd, start = start bdd\<rparr> = bdd" by simp

lemma reachable_inv_startI: "abdd_reachable \<lparr> nodes = n, start = x \<rparr> a b \<Longrightarrow> abdd_reachable \<lparr> nodes = n, start = y \<rparr> a b"
	by(induction "\<lparr> nodes = n, start = x \<rparr>" a b rule: abdd_reachable.induct)
	(simp_all add: ar_base ar_step)
lemma reachable_inv_start: "abdd_reachable \<lparr> nodes = n, start = x \<rparr> a b = abdd_reachable \<lparr> nodes = n, start = y \<rparr> a b"
	using reachable_inv_startI by blast

termination abstract_abdd3
proof(relation "measure (\<lambda>bdd. case getnode bdd (start bdd) of Some n \<Rightarrow> card (abdd_reachable_set bdd n) | None \<Rightarrow> 0)",
	rule wf_measure)
	case goal1
	then have as: "abdd_reference_integrity bdd" "abdd_cycle_free bdd" by simp_all
	have xe: "x \<in> set (nodes bdd)" using as(1) getnode_in3 goal1(2) goal1(3) by fastforce  
	have cs: "(case getnode bdd (right x) of None \<Rightarrow> 0 | Some n \<Rightarrow> card (abdd_reachable_set bdd n)) =
		card (abdd_reachable_set bdd  (the (getnode bdd (right x))))" using node_gettable(1)[OF xe as(1)] by force
	have start_in: "start bdd \<in> set (abdd_collect_refs bdd)" unfolding abdd_collect_refs_def by simp
	note psubset_card_mono[OF abdd_reachable_fin step_reachable_rsubset_r[OF as(2) xe as(1)]]
	then show ?case
		unfolding in_measure
		unfolding getnode_start_inv[of "nodes bdd" "right x" _ "start bdd"]
		unfolding abdd.simps
		unfolding abdd_reachable_set_def
		unfolding reachable_inv_start[of "nodes bdd" "right x" _ _ "start bdd"]
		unfolding abdd_simp_instance
		unfolding abdd_reachable_set_def[symmetric]
		unfolding cs
		using getnode_noNone[OF start_in as(1)]
		using goal1(2) goal1(3) by force
next
	case goal2
	then have as: "abdd_reference_integrity bdd" "abdd_cycle_free bdd" by simp_all
	have xe: "x \<in> set (nodes bdd)" using as(1) getnode_in3 goal2(2) goal2(3) by fastforce  
	have cs: "(case getnode bdd (left x) of None \<Rightarrow> 0 | Some n \<Rightarrow> card (abdd_reachable_set bdd n)) =
		card (abdd_reachable_set bdd  (the (getnode bdd (left x))))" using node_gettable(2)[OF xe as(1)] by force
	have start_in: "start bdd \<in> set (abdd_collect_refs bdd)" unfolding abdd_collect_refs_def by simp
	note psubset_card_mono[OF abdd_reachable_fin step_reachable_rsubset_l[OF as(2) xe as(1)]]
	then show ?case
		unfolding in_measure
		unfolding getnode_start_inv[of "nodes bdd" "left x" _ "start bdd"]
		unfolding abdd.simps
		unfolding abdd_reachable_set_def
		unfolding reachable_inv_start[of "nodes bdd" "left x" _ _ "start bdd"]
		unfolding abdd_simp_instance
		unfolding abdd_reachable_set_def[symmetric]
		unfolding cs
		using getnode_noNone[OF start_in as(1)]
		using goal2(2) goal2(3)
		by force
qed

definition "abstract_abdd bdd = abstract_abdd2 bdd (start bdd)"

definition "abdd_restrict_top bdd val = \<lparr> nodes = nodes bdd, 
	start = ((if val then right else left) \<circ> the \<circ> getnode bdd \<circ> start) bdd  \<rparr>"
	
lemma ref_integr_inv_startI: "y \<in> set (abdd_collect_refs \<lparr> nodes = n, start = x \<rparr>) \<Longrightarrow> 
	abdd_reference_integrity \<lparr> nodes = n, start = x \<rparr> \<Longrightarrow> abdd_reference_integrity \<lparr> nodes = n, start = y \<rparr>"
	unfolding abdd_reference_integrity_def
	unfolding abdd_collect_refs_def
	unfolding abdd.simps
	by auto
	(* In hindsight, it is scary that this is provable automatically *)
lemma abdd_reference_integrity_children:
	assumes "abdd_reference_integrity bdd" 
	shows "abdd_reference_integrity \<lparr> nodes = nodes bdd, start = right (the (getnode bdd (start bdd)))  \<rparr>"
		"abdd_reference_integrity \<lparr> nodes = nodes bdd, start = left (the (getnode bdd (start bdd)))  \<rparr>"
using assms
proof -
	assume san: "abdd_reference_integrity bdd"
	have si: "start bdd \<in> set (abdd_collect_refs bdd)" 
		unfolding abdd_collect_refs_def by simp
	obtain nod where nod: "Some nod = getnode bdd (start bdd)"
		using san getnode_noNone[OF si san] by fastforce
	then have nodeq: "the (getnode bdd (start bdd)) = nod"
		using option.sel by metis
	then have "nod \<in> set (nodes bdd)"
		using getnode_in3 san by blast 
	then have "right nod \<in> set (abdd_collect_refs bdd)" "left nod \<in> set (abdd_collect_refs bdd)"
		unfolding abdd_collect_refs_def by simp_all
	then show "abdd_reference_integrity \<lparr>nodes = nodes bdd, start = right (the (getnode bdd (start bdd)))\<rparr>"
		"abdd_reference_integrity \<lparr>nodes = nodes bdd, start = left (the (getnode bdd (start bdd)))\<rparr>"
		using san nodeq abdd_simp_instance ref_integr_inv_startI
		by metis+
qed

lemma
	assumes "abdd_reference_integrity bdd"
	shows "abdd_reference_integrity (abdd_restrict_top bdd val)"
	unfolding abdd_restrict_top_def
	using assms
	unfolding abdd_reference_integrity_def
	proof -
		case goal1
		have "set (abdd_collect_refs \<lparr>nodes = nodes bdd, 
			start = ((if val then right else left) \<circ> the \<circ> getnode bdd \<circ> start) bdd\<rparr>)
			\<subseteq> set (abdd_collect_refs bdd)"
			unfolding comp_def
			unfolding abdd_collect_refs_def
			unfolding abdd.simps
			unfolding set_simps set_append
			using getnode_in3[OF assms]
			by fastforce
		thus ?case using goal1 by fastforce
	qed

lemma cycle_free_inv_startI: "abdd_cycle_free \<lparr> nodes = n, start = x \<rparr> \<Longrightarrow> abdd_cycle_free \<lparr> nodes = n, start = y \<rparr>"
	unfolding abdd_cycle_free_def
	using reachable_inv_startI
	proof - qed auto
lemma cycle_free_inv_start: "abdd_cycle_free \<lparr> nodes = nodes bdd, start = x \<rparr> = abdd_cycle_free bdd"
	using cycle_free_inv_startI abdd_simp_instance
	by metis

lemma
	assumes "abdd_cycle_free bdd"
	shows "abdd_cycle_free (abdd_restrict_top bdd val)"
	using assms
	unfolding abdd_cycle_free_def
	unfolding abdd_restrict_top_def
	unfolding abdd.simps
	unfolding reachable_inv_start[of "nodes bdd" 
		"((if val then right else left) \<circ> the \<circ> getnode bdd \<circ> start) bdd" _ _ "start bdd"]
	unfolding abdd_simp_instance
	.

lemma 
	assumes "abdd_reference_integrity bdd \<and> abdd_cycle_free bdd"
	shows "abstract_abdd bdd = abstract_abdd3 bdd"
unfolding abstract_abdd_def
using assms
proof(induction rule: abstract_abdd3.induct)
	case goal1
	note val = goal1(3)
	note mih = goal1(2)[OF goal1(3)] goal1(1)[OF goal1(3)]
	show ?case
	proof(cases "start bdd")
		case goal2 with val show ?case by simp
	next
		case goal3 with val show ?case by simp
	next
		case goal1
		note mmih = mih[OF goal1, of "the (getnode bdd (LabeledNode x1))", unfolded cycle_free_inv_start abdd.simps]
	oops

lemma abstract_abdd_inv_startI: "t = \<lparr> nodes = n, start = x \<rparr> \<Longrightarrow> q = \<lparr> nodes = n, start = y \<rparr> \<Longrightarrow> 
	abstract_abdd2 t a b \<Longrightarrow> abstract_abdd2 q a b"
proof(induction rule: abstract_abdd2.induct, simp, simp)
	case goal1
	show ?case (is ?kees)
	proof(cases "abdd_reference_integrity bdd \<and> abdd_cycle_free bdd")
		have cr: "y \<in> set (abdd_collect_refs \<lparr>nodes = n, start = x\<rparr>)"  sorry
		case False
		hence "\<not> (abdd_reference_integrity t \<and> abdd_cycle_free t)" 
			unfolding goal1(3) goal1(4) using cycle_free_inv_startI ref_integr_inv_startI[OF cr] by blast 
		thus ?kees
			using goal1(5) 
			unfolding abstract_abdd2.simps
			by(simp only: if_False)
	next
		case True
		note mih = goal1(1)[OF True _ _ goal1(3) goal1(4)]
oops

lemma 
	assumes san: "abdd_reference_integrity bdd" "abdd_cycle_free bdd"
	assumes tv: "k = var (the (getnode bdd (start bdd)))"
	shows "abstract_abdd (abdd_restrict_top bdd val) as = bf2_restrict k val (abstract_abdd bdd) as"
proof
	assume "abstract_abdd (abdd_restrict_top bdd val) as"
	note k = this[unfolded abstract_abdd_def abdd_restrict_top_def abdd.simps]
oops

lemma 
	assumes san: "abdd_reference_integrity bdd" "abdd_cycle_free bdd"
	assumes tv: "k = var (the (getnode bdd (start bdd)))"
	shows "abstract_abdd3 (abdd_restrict_top bdd val) as = bf2_restrict k val (abstract_abdd3 bdd) as"
proof
	assume "abstract_abdd3 (abdd_restrict_top bdd val) as"
	note k = this[unfolded abdd_restrict_top_def abdd.simps]
	thus "bf2_restrict k val (abstract_abdd3 bdd) as"
		unfolding bf2_restrict_def
		unfolding tv
		apply(cases val)
		apply(simp add: san)
oops

definition "abstract_abdd4 bdd as = 
	(let plain = map (\<lambda>node. (label node, if as (var node) then right node else left node)) (nodes bdd) in let tc = trancl (set plain) in
	case ((start bdd, DTrue) \<in> tc, (start bdd, DFalse) \<in> tc) of
		(True, False) \<Rightarrow> True |
		(False, True) \<Rightarrow> False |
		_ \<Rightarrow> undefined)"
value "map (abstract_abdd4 abdd_xor) 
	[(\<lambda>i. [False, False] ! i), (\<lambda>i. [False, True] ! i), (\<lambda>i. [True, False] ! i), (\<lambda>i. [True, True] ! i)]"


end
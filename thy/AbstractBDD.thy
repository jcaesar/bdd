theory AbstractBDD
imports BoolFunc
begin

record abdd_node =
	variable :: nat (* evaluated variable *)
	right :: nat (* true branch *)
	left :: nat (* false branch *)
	
record abdd =
	nodecount :: "nat"
	nodes :: "nat \<Rightarrow> abdd_node"
(* the idea is that the bdd is written down as a linear program with a decreasing pointer to a node *)
(* node 0 is always just false and 1 just true and does not have to be defined *)
(* I'm not sure that the nodecount should be part of the thing. Sometimes we don't need it, and then proofs get ugly. *)

value "upt 3 5"
value "upt 0 0"

definition "abdd_nodeset bdd = set (map (nodes bdd) (upt 2 (nodecount bdd)))"
definition abdd_ref_int :: "abdd \<Rightarrow> bool" where
	"abdd_ref_int bdd \<equiv> (\<forall>node \<in> abdd_nodeset bdd. left node < nodecount bdd \<and> right node < nodecount bdd)"
definition "abdd_linear bdd = (\<forall>i \<in> {2..<nodecount bdd}. let n = nodes bdd i in left n < i \<and> right n < i)"
lemma "abdd_linear bdd \<Longrightarrow> abdd_ref_int bdd"
	unfolding abdd_linear_def abdd_ref_int_def Let_def abdd_nodeset_def
	unfolding set_map set_upt
	proof
		case goal1
		obtain i where i: "i \<in> {2..<nodecount bdd}" "node = nodes bdd i"
			using goal1(2) by blast
		then have "left (nodes bdd i) < i \<and> right (nodes bdd i) < i"
			using goal1(1) by simp
		then have "left (nodes bdd i) < nodecount bdd \<and> right (nodes bdd i) < nodecount bdd"
			using i(1) by simp
		then show ?case
			unfolding i(2)
		.
	qed
lemma abdd_linear_le: "2 \<le> x \<Longrightarrow> abdd_linear bdd \<and> x < nodecount bdd \<Longrightarrow> left (nodes bdd x) < x \<and> right (nodes bdd x) < x"
	unfolding abdd_linear_def Let_def
	proof -
		case goal1
		hence "x \<in> {2..<nodecount bdd}" by simp
		thus ?case using goal1(2) by fastforce
	qed
		
definition "abdd_terminal state = (state \<le> 1)" 
definition "abdd_xor \<equiv> \<lparr> nodecount = 5, nodes = (\<lambda>i. [undefined, undefined,
	\<lparr> variable = 0, right = 1, left = 0 \<rparr>,
	\<lparr> variable = 0, right = 0, left = 1 \<rparr>,
	\<lparr> variable = 1, right = 3, left = 2 \<rparr>] ! i)
\<rparr>"
lemma[code]: "abdd_linear abdd_xor = True"
	unfolding eq_True
	unfolding abdd_linear_def abdd_xor_def
	unfolding abdd.simps
	unfolding Let_def
	apply clarify
	unfolding Set_Interval.ord_class.atLeastLessThan_iff
	apply(case_tac "i = 2", simp)
	apply(case_tac "i = 3", simp)
	apply(case_tac "i = 4", simp)
	by force

function abstract_abdd :: "abdd \<Rightarrow> nat \<Rightarrow> boolfunc2" where
"abstract_abdd bdd 0 = (\<lambda>_. False)" |
"abstract_abdd bdd (Suc 0) = (\<lambda>_. True)" |
"abstract_abdd bdd (Suc (Suc dn)) = (let n = Suc (Suc dn) in (if abdd_linear bdd \<and> n < nodecount bdd
	then (\<lambda>as. let nod = nodes bdd n in (if as (variable nod) then abstract_abdd bdd (right nod) as else abstract_abdd bdd (left nod) as))
	else undefined))"
by pat_completeness auto

termination abstract_abdd
proof(relation "measure (\<lambda>(bdd, nl). nl)",	rule wf_measure, unfold in_measure, simp_all)
	fix dn x xa xb
	let ?x = "Suc (Suc dn)"
	fix bdd :: abdd
	assume sucsuc: "x = Suc (Suc dn)"
    assume val: "abdd_linear bdd \<and> ?x < nodecount bdd"
    assume xbd: "xb = nodes bdd ?x"
	have "2 \<le> ?x" using sucsuc by simp
	then show "right (nodes bdd ?x) < ?x" "left (nodes bdd ?x) < ?x"
		using val unfolding abdd_linear_def unfolding Let_def by(simp_all add: xbd)
qed

(* In hindsight: Why do I need a function? fun does the trick. *)
fun abstract_abdd3 :: "abdd \<Rightarrow> nat \<Rightarrow> boolfunc2" where
"abstract_abdd3 bdd 0 = (\<lambda>_. False)" |
"abstract_abdd3 bdd (Suc 0) = (\<lambda>_. True)" |
"abstract_abdd3 bdd (Suc (Suc dn)) = (*(let n = Suc (Suc dn) in 
		(\<lambda>as. let nod = nodes bdd n ; next = (if as (variable nod) then right nod else left nod) in (if next < n then abstract_abdd3 bdd next as else undefined)))*)
		(\<lambda>as. if (if as (variable (nodes bdd (Suc (Suc dn)))) then right (nodes bdd (Suc (Suc dn))) else left (nodes bdd (Suc (Suc dn)))) < Suc (Suc dn)
         then abstract_abdd3 bdd (if as (variable (nodes bdd (Suc (Suc dn)))) then right (nodes bdd (Suc (Suc dn))) else left (nodes bdd (Suc (Suc dn)))) as else undefined)
		"

lemma twolesucsuc: "2 \<le> Suc (Suc dn)" by simp

lemma abdd_linear_3_eq: "abdd_linear bdd \<and> n < nodecount bdd \<Longrightarrow> abstract_abdd bdd n as = abstract_abdd3 bdd n as"
proof(induction rule: abstract_abdd3.induct)
	case goal3
	note k = goal3(1)[of as]
	thus ?case (is ?kees)
	proof(cases "as (variable (nodes bdd (Suc (Suc dn))))")
		case True
		have le: "right (nodes bdd (Suc (Suc dn))) < Suc (Suc dn)" "right (nodes bdd (Suc (Suc dn))) < nodecount bdd"
			using abdd_linear_le[OF twolesucsuc goal3(2)] goal3(2) by simp_all
		show ?kees using k 
			by(simp only: True if_True le goal3(2) simp_thms abstract_abdd.simps abstract_abdd3.simps Let_def)
	next
		case False
		have le: "left (nodes bdd (Suc (Suc dn))) < Suc (Suc dn)" "left (nodes bdd (Suc (Suc dn))) < nodecount bdd"
			using abdd_linear_le[OF twolesucsuc goal3(2)] goal3(2) by simp_all
		show ?kees using k 
			by(simp only: False if_True if_False le goal3(2) simp_thms abstract_abdd.simps abstract_abdd3.simps Let_def)
	qed
qed simp_all


definition "abdd_to_graph bdd as \<equiv> 
	(let plain = map (\<lambda>nl. (nl, if as (variable (nodes bdd nl)) then right (nodes bdd nl) else left (nodes bdd nl))) (upt 2 (nodecount bdd)) 
	in {(0,0),(1,1)} \<union> trancl (set plain))"

definition "abstract_abdd2 bdd start as = 
	(case ((start, 1) \<in> abdd_to_graph bdd as, (start, 0) \<in> abdd_to_graph bdd as) of
		(True, False) \<Rightarrow> True |
		(False, True) \<Rightarrow> False |
		_ \<Rightarrow> False)" (* miraculously more helpful than undefined *)		

value "map (abstract_abdd2 abdd_xor (nodecount abdd_xor - 1)) 
	[(\<lambda>i. [False, False] ! i), (\<lambda>i. [False, True] ! i), (\<lambda>i. [True, False] ! i), (\<lambda>i. [True, True] ! i)]" (* meh. :( *)
value "(\<lambda>bdd start as. let plain = map (\<lambda>nl. (nl, if as (variable (nodes bdd nl)) then right (nodes bdd nl) else left (nodes bdd nl))) (upt 2 (nodecount bdd));
	tc = trancl (set plain) in (plain)) abdd_xor 5 (\<lambda>i. [True, True] ! i)"
	
lemma notin_un: "x \<notin> a \<Longrightarrow> x \<notin> b \<Longrightarrow> x \<notin> (a \<union> b)" by simp

lemma trancl_monoI: "a \<subseteq> b \<Longrightarrow> trancl a \<subseteq> trancl b"
	by (simp add: subsetI trancl_mono)

lemma abstract_abdd_eq_hlp1: "\<not>abstract_abdd2 bdd 0 as" "abstract_abdd2 bdd 1 as"
proof -
	have 1: "\<And>f. set (map (\<lambda>nl. (nl, f nl)) [2..<nodecount bdd]) \<subseteq> {(a,b)|a b. 2 \<le> a}"
		unfolding set_map set_upt
		using atLeastLessThan_iff by blast
	have 2: "{(a,b)|a b. 2 \<le> a} = trancl {(a,b)|a b. 2 \<le> a}"
	proof(rule, blast, rule)
		case goal1
		obtain m n where mn: "(m, n) = x" using surj_pair by metis
		then have "2 \<le> m" using goal1
		proof - (* sletschhemmer *)
		  obtain bb :: "('b \<times> 'b) set \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b" where
			f1: "\<forall>x0 x1 x2. (\<exists>v3. (x2, v3) \<in> x0 \<and> (v3, x1) \<in> x0\<^sup>+) = ((x2, bb x0 x1 x2) \<in> x0 \<and> (bb x0 x1 x2, x1) \<in> x0\<^sup>+)"
			by moura
		  have "(m, n) \<in> {(b, ba) |b ba. 2 \<le> b}\<^sup>+"
			using `x \<in> {(a, b) |a b. 2 \<le> a}\<^sup>+` by (simp add: mn)
		  hence "(m, n) \<in> {(b, ba) |b ba. 2 \<le> b} \<or> (m, bb {(b, ba) |b ba. 2 \<le> b} n m) \<in> {(b, ba) |b ba. 2 \<le> b} \<and> (bb {(b, ba) |b ba. 2 \<le> b} n m, n) \<in> {(b, ba) |b ba. 2 \<le> b}\<^sup>+"
			using f1 by (meson converse_tranclE)
		  thus ?thesis
			by blast
		qed
		thus ?case unfolding mn[symmetric] by blast
	qed
	let ?foo = "{(0, 0), (1, 1)} \<union> (set (map (\<lambda>nl. (nl, if as (variable (nodes bdd nl)) then right (nodes bdd nl) else left (nodes bdd nl))) [2..<nodecount bdd]))\<^sup>+"
	have 3: "(0,1) \<notin> ?foo"
		apply(rule notin_un, eval) 
		apply(rule contra_subsetD[of _ "{(a,b)|a b. 2 \<le> a}"])
		apply(subst 2)
		apply(rule trancl_monoI) 
		using 1 by fastforce+
	have 4: "(1,0) \<notin> ?foo"
		apply(rule notin_un, eval) 
		apply(rule contra_subsetD[of _ "{(a,b)|a b. 2 \<le> a}"])
		apply(subst 2)
		apply(rule trancl_monoI) 
		using 1 by fastforce+
	have 5: "(0,0) \<in> ?foo" "(1,1) \<in> ?foo" by blast+
	show "\<not>abstract_abdd2 bdd 0 as" "abstract_abdd2 bdd 1 as" unfolding abstract_abdd2_def abdd_to_graph_def Let_def  using 3 4 5 by simp_all
qed

lemma case_defeat: "(case (a, b) of 
	(True, True) \<Rightarrow> w |
	(True, False) \<Rightarrow> x |
	(False, True) \<Rightarrow> y |
	(False, False) \<Rightarrow> z) = 
	(if a then (if b then w else x) else (if b then y else z))"
by simp

lemma trancl_onepath: "(a, c) \<in> trancl x \<Longrightarrow> b \<noteq> c \<Longrightarrow> (\<And>k. (a,k) \<in> x \<Longrightarrow> k = b) \<Longrightarrow>
	(b, c) \<in> trancl x"
	by (metis rtranclD tranclD)

lemma abstract_abdd2_istep_right: "as (variable (nodes bdd (Suc (Suc dn)))) \<Longrightarrow> Suc (Suc dn) < nodecount bdd \<Longrightarrow>
	abstract_abdd2 bdd (Suc (Suc dn)) as = abstract_abdd2 bdd (right (nodes bdd (Suc (Suc dn)))) as"
proof -
	let ?x = "Suc (Suc dn)"
	let ?bs = "set (map (\<lambda>nl. (nl, if as (variable (nodes bdd nl)) 
	then right (nodes bdd nl) else left (nodes bdd nl))) [2..<nodecount bdd])"
	let ?mors = "{(0, 0), (1, 1)} \<union> ?bs\<^sup>+"
	note dteam = abstract_abdd2_def abdd_to_graph_def Let_def case_defeat
	case goal1
	have pe: "(Suc (Suc dn), right (nodes bdd (Suc (Suc dn)))) \<in> 
		?bs" (is "?pe \<in> ?bs")
		using goal1
		proof -
			have s: "[2..<nodecount bdd] = [2..<?x] @ (?x # [Suc ?x..<nodecount bdd])"
				thm upt_conv_Cons
				unfolding upt_conv_Cons[OF goal1(2), symmetric]
				using upt_add_eq_append[of 2 ?x "nodecount bdd - ?x"] goal1(2)
				by (metis Suc_le_mono le0 le_add_diff_inverse less_imp_le numeral_2_eq_2)
			case goal1 show ?case
				unfolding s
				unfolding map_append list.map(2)
				unfolding set_map set_append set_simps
				by(simp only: goal1(1) if_True) blast
		qed
	have i: "\<And>k. (Suc (Suc dn), k) \<in> ?bs \<Longrightarrow> k = right (nodes bdd (Suc (Suc dn)))"
		using pe by auto
	show ?case proof
		case goal1
		have 0: "(Suc (Suc dn), 0) \<notin> ?mors" "(Suc (Suc dn), 1) \<in> ?mors" 
			using goal1
			unfolding dteam
			by presburger+
		then have 1: "(Suc (Suc dn), 0) \<notin> ?bs\<^sup>+" "(Suc (Suc dn), 1) \<in> ?bs\<^sup>+" by simp_all
		have 2: "?pe \<in> ?mors" using pe by simp
		have 3: "(right (nodes bdd (Suc (Suc dn))), 1) \<in> ?mors"
			using trancl_onepath[OF 1(2) _ i]
			by(cases "(right (nodes bdd (Suc (Suc dn)))) = 1") simp_all
		have 4: "right (nodes bdd (Suc (Suc dn))) \<noteq> 0" 
			using goal1
			unfolding dteam if_cancel
			using 2 by metis
		have 5: "(right (nodes bdd (Suc (Suc dn))), 0) \<notin> ?bs\<^sup>+"
		proof(rule ccontr, unfold not_not)
			case goal1
			hence "(Suc (Suc dn), 0) \<in> ?bs\<^sup>+" using pe by simp
			thus False using 1(1) by blast
		qed
		with 4 have 6: "(right (nodes bdd (Suc (Suc dn))), 0) \<notin> ?mors" by force
		show ?case
			unfolding dteam
			by(simp only: 3 if_True 6 if_False)
	next
		case goal2
		have 1: "(right (nodes bdd (Suc (Suc dn))), 1) \<in> ?mors"
			using goal2 unfolding dteam
			by meson
		have a: "(Suc (Suc dn), 1) \<in> ?mors" 
			using pe 1
			by(cases "right (nodes bdd (Suc (Suc dn))) = 1") simp_all
		have 2: "(right (nodes bdd (Suc (Suc dn))), 0) \<notin> ?bs\<^sup>+"
			using goal2 unfolding dteam if_cancel by (meson UnI2)
		have 4: "right (nodes bdd (Suc (Suc dn))) \<noteq> 0"
		proof(rule ccontr, unfold not_not)
			case goal1
			note goal2[unfolded dteam if_cancel goal1]
			then show False by(cases "(0, 1) \<in> ?mors") simp_all 
		qed
		have 3: "(right (nodes bdd (Suc (Suc dn))), 0) \<notin> ?mors"
			using 2 4 by simp
		have b: "(Suc (Suc dn), 0) \<notin> ?mors"
		proof(rule ccontr, unfold not_not)
			case goal1
			then have "(Suc (Suc dn), 0) \<in> ?bs\<^sup>+" by force
			with pe have "(right (nodes bdd (Suc (Suc dn))), 0) \<in> ?mors" by (simp add: 4 i trancl_onepath)
			with 3 show False ..
		qed
		show ?case
			unfolding dteam
			by(simp only: a b if_True if_False)
	qed
qed

lemma abstract_abdd2_istep_left: "\<not>as (variable (nodes bdd (Suc (Suc dn)))) \<Longrightarrow> Suc (Suc dn) < nodecount bdd \<Longrightarrow>
	abstract_abdd2 bdd (Suc (Suc dn)) as = abstract_abdd2 bdd (left (nodes bdd (Suc (Suc dn)))) as"
proof -
	let ?x = "Suc (Suc dn)"
	let ?bs = "set (map (\<lambda>nl. (nl, if as (variable (nodes bdd nl)) 
	then right (nodes bdd nl) else left (nodes bdd nl))) [2..<nodecount bdd])"
	let ?mors = "{(0, 0), (1, 1)} \<union> ?bs\<^sup>+"
	note dteam = abstract_abdd2_def abdd_to_graph_def Let_def case_defeat
	case goal1
	have pe: "(Suc (Suc dn), left (nodes bdd (Suc (Suc dn)))) \<in> 
		?bs" (is "?pe \<in> ?bs")
		using goal1
		proof -
			have s: "[2..<nodecount bdd] = [2..<?x] @ (?x # [Suc ?x..<nodecount bdd])"
				unfolding upt_conv_Cons[OF goal1(2), symmetric]
				using upt_add_eq_append[of 2 ?x "nodecount bdd - ?x"] goal1(2)
				by (metis Suc_le_mono le0 le_add_diff_inverse less_imp_le numeral_2_eq_2)
			case goal1 show ?case
				unfolding s
				unfolding map_append list.map(2)
				unfolding set_map set_append set_simps
				by(simp only: goal1(1) if_False) blast
		qed
	have i: "\<And>k. (Suc (Suc dn), k) \<in> ?bs \<Longrightarrow> k = left (nodes bdd (Suc (Suc dn)))"
		using pe by auto
	show ?case proof
		case goal1
		have 0: "(Suc (Suc dn), 0) \<notin> ?mors" "(Suc (Suc dn), 1) \<in> ?mors"
			using goal1
			unfolding dteam
			by presburger+
		then have 1: "(Suc (Suc dn), 0) \<notin> ?bs\<^sup>+" "(Suc (Suc dn), 1) \<in> ?bs\<^sup>+" by simp_all
		have 2: "?pe \<in> ?mors" using pe by simp
		have 3: "(left (nodes bdd (Suc (Suc dn))), 1) \<in> ?mors"
			using trancl_onepath[OF 1(2) _ i]
			by(cases "(left (nodes bdd (Suc (Suc dn)))) = 1") simp_all
		have 4: "left (nodes bdd (Suc (Suc dn))) \<noteq> 0" 
			using goal1
			unfolding dteam if_cancel
			using 2 by metis
		have 5: "(left (nodes bdd (Suc (Suc dn))), 0) \<notin> ?bs\<^sup>+"
		proof(rule ccontr, unfold not_not)
			case goal1
			hence "(Suc (Suc dn), 0) \<in> ?bs\<^sup>+" using pe by simp
			thus False using 1(1) by blast
		qed
		with 4 have 6: "(left (nodes bdd (Suc (Suc dn))), 0) \<notin> ?mors" by force
		show ?case
			unfolding dteam
			by(simp only: 3 if_True 6 if_False)
	next
		case goal2
		have a: "(Suc (Suc dn), 1) \<in> ?mors" (is ?theess)
		proof -
			have 1: "(left (nodes bdd (Suc (Suc dn))), 1) \<in> ?mors"
				using goal2 unfolding dteam
				by meson
			show ?theess
				using pe 1
				by(cases "left (nodes bdd (Suc (Suc dn))) = 1") simp_all
		qed
		have b: "(Suc (Suc dn), 0) \<notin> ?mors"
		proof(rule ccontr, unfold not_not)
			have 2: "(left (nodes bdd (Suc (Suc dn))), 0) \<notin> ?bs\<^sup>+"
				using goal2 unfolding dteam if_cancel by (meson UnI2)
			have 4: "left (nodes bdd (Suc (Suc dn))) \<noteq> 0"
			proof(rule ccontr, unfold not_not)
				case goal1
				note goal2[unfolded dteam if_cancel goal1]
				then show False by(cases "(0, 1) \<in> ?mors") simp_all 
			qed
			have 3: "(left (nodes bdd (Suc (Suc dn))), 0) \<notin> ?mors"
				using 2 4 by simp
			case goal1
			then have "(Suc (Suc dn), 0) \<in> ?bs\<^sup>+" by force
			with pe have "(left (nodes bdd (Suc (Suc dn))), 0) \<in> ?mors" by (simp add: 4 i trancl_onepath)
			with 3 show False ..
		qed
		show ?case
			unfolding dteam
			by(simp only: a b if_True if_False)
	qed
qed

lemma abstract_abdd_eq: "abdd_linear bdd \<and> start < nodecount bdd \<Longrightarrow> abstract_abdd bdd start as = abstract_abdd2 bdd start as"
proof(induction rule: abstract_abdd.induct, simp add: abstract_abdd_eq_hlp1(1))
	case goal1 show ?case using abstract_abdd_eq_hlp1(2) by auto (* try simp. weird. *)
next
	case goal2
	have "right (nodes bdd (Suc (Suc dn))) < (Suc (Suc dn))" using goal2(3) unfolding abdd_linear_def Let_def by force
	then have 1: "abdd_linear bdd \<and> right (nodes bdd (Suc (Suc dn))) < nodecount bdd" using goal2(3) by linarith
	have "left (nodes bdd (Suc (Suc dn))) < (Suc (Suc dn))" using goal2(3) unfolding abdd_linear_def Let_def by force
	then have 2: "abdd_linear bdd \<and> left (nodes bdd (Suc (Suc dn))) < nodecount bdd" using goal2(3) by linarith
	show ?case (is ?kees)
	proof(cases "as (variable (nodes bdd (Suc (Suc dn))))")
		case True
		note k = goal2(1)[OF refl goal2(3) refl _ 1, of as]
		show ?kees  by(simp only: abstract_abdd.simps Let_def goal2(3) simp_thms if_True True k[OF True] abstract_abdd2_istep_right)
	next
		case False
		note k = goal2(2)[OF refl _ refl _ 2, of as]
		show ?kees by(simp only: abstract_abdd.simps Let_def goal2(3) simp_thms if_False if_True False k abstract_abdd2_istep_left)
	qed
qed

definition "abdd_restrict bdd var val =
	\<lparr> nodecount = nodecount bdd, nodes = 
		(\<lambda>i.(let n = nodes bdd i; ptr = (if val then right else left) n in if variable n = var 
			then \<lparr> variable = variable n, right = ptr, left = ptr \<rparr> else nodes bdd i))
	\<rparr>"
(* Dunno if I'm going to use that. *)

definition "abdd_ordered bdd \<equiv> (\<forall>i \<in> {2..<nodecount bdd}. 
	let nd = (\<lambda>f i. f (nodes bdd i));
	c = (\<lambda>f. abdd_terminal (nd f i) \<or> nd variable (nd f i) < nd variable i)
	in (c left \<and> c right))"
lemma "abdd_ordered abdd_xor"
	unfolding abdd_ordered_def abdd_xor_def Let_def abdd_terminal_def
	apply clarify
	apply(case_tac "i = 2", simp)
	apply(case_tac "i = 3", simp)
	apply(case_tac "i = 4", simp)
	apply(simp)
done

lemma nat_2_case: "(x = 0 \<Longrightarrow> P) \<Longrightarrow> (x = Suc 0 \<Longrightarrow> P) \<Longrightarrow> (\<And>va. x = Suc (Suc va) \<Longrightarrow> P) \<Longrightarrow> P"
using not0_implies_Suc by blast

lemma nat_2_case_only: "\<not>2 \<le> x \<Longrightarrow> (x = 0 \<Longrightarrow> P) \<Longrightarrow> (x = Suc 0 \<Longrightarrow> P) \<Longrightarrow> P" by fastforce

lemma linear_notouch: "abdd_linear bdd \<and> x < nodecount bdd \<Longrightarrow> variable (nodes bdd x) < k 
		\<Longrightarrow> abdd_ordered bdd \<Longrightarrow>
       abstract_abdd3 bdd x (as(k := True)) = abstract_abdd3 bdd x as"
proof(induction rule: abstract_abdd3.induct, simp, simp)
	case goal1
	thus ?case (is ?kees)
	proof(cases "as (variable (nodes bdd (Suc (Suc dn))))")
		case True
		have 1: "right (nodes bdd (Suc (Suc dn))) < Suc (Suc dn)" using goal1(2) by (simp add: abdd_linear_le)
		have 3: "(as(k := True)) (variable (nodes bdd (Suc (Suc dn)))) = as (variable (nodes bdd (Suc (Suc dn))))"
			using goal1(3) by auto
		note magicsimpset = True if_True 1 goal1(2) goal1(4) less_trans[OF 1] abstract_abdd3.simps 3
		show ?kees
		proof(cases "2 \<le> right (nodes bdd (Suc (Suc dn)))")
			case True
			have 2: "variable (nodes bdd (right (nodes bdd (Suc (Suc dn))))) < variable (nodes bdd (Suc (Suc dn)))"
				using goal1(4)[unfolded abdd_ordered_def] True goal1(2)
				unfolding Let_def abdd_terminal_def
				by (metis One_nat_def atLeastLessThan_iff not_less_eq_eq numeral_2_eq_2 twolesucsuc) 
			show ?kees
				using goal1(1)[of as]
				by(simp only: magicsimpset less_trans[OF 2 goal1(3)])
		next
			{
				fix x P
				have "\<not>2 \<le> x \<Longrightarrow> (x = 0 \<Longrightarrow> P) \<Longrightarrow> (x = Suc 0 \<Longrightarrow> P) \<Longrightarrow> P" by fastforce
			} note twocase = this
			case False
			show ?kees
				unfolding abstract_abdd3.simps
				unfolding 3
				by (cases rule: twocase[OF False]) (simp_all only: magicsimpset)
		qed
	next
		case False
		have 1: "left (nodes bdd (Suc (Suc dn))) < Suc (Suc dn)" using goal1(2) by (simp add: abdd_linear_le)
		have 3: "(as(k := True)) (variable (nodes bdd (Suc (Suc dn)))) = as (variable (nodes bdd (Suc (Suc dn))))"
			using goal1(3) by auto
		note magicsimpset = False if_False if_True 1 goal1(2) goal1(4) less_trans[OF 1] abstract_abdd3.simps 3
		show ?kees
		proof(cases "2 \<le> left (nodes bdd (Suc (Suc dn)))")
			case True
			have 2: "variable (nodes bdd (left (nodes bdd (Suc (Suc dn))))) < variable (nodes bdd (Suc (Suc dn)))"
				using goal1(4)[unfolded abdd_ordered_def] True goal1(2)
				unfolding Let_def abdd_terminal_def
				by (metis One_nat_def atLeastLessThan_iff not_less_eq_eq numeral_2_eq_2 twolesucsuc)
			show ?kees
				using goal1(1)[of as]
				by(simp only: magicsimpset less_trans[OF 2 goal1(3)] simp_thms)
		next
			case False
			show ?kees
				unfolding abstract_abdd3.simps
				unfolding 3
				by(cases rule: nat_2_case_only[OF False]) (simp_all only: magicsimpset)
		qed
	qed
qed

lemma 
	assumes san: "abdd_linear bdd \<and> x < nodecount bdd" "2 \<le> x"
	assumes only: "abdd_ordered bdd"
	shows "abstract_abdd bdd (right (nodes bdd x)) as = bf2_restrict (variable (nodes bdd x)) True (abstract_abdd bdd x) as"
using assms
proof(induction rule: abstract_abdd3.induct, simp, simp)
	case goal1
	note goal = goal1
	note to3 = abdd_linear_3_eq[OF goal1(2)]
	have le: "right (nodes bdd (Suc (Suc dn))) < Suc (Suc dn)" "right (nodes bdd (Suc (Suc dn))) < nodecount bdd"
	using abdd_linear_le[OF twolesucsuc goal(2)] goal(2) by simp_all
	show ?case unfolding bf2_restrict_def to3
	proof(cases "as (variable (nodes bdd (Suc (Suc dn))))")
		case goal1
		thus ?case
			apply(simp only: abstract_abdd3.simps fun_upd_idem if_True le)
			apply(case_tac "right (nodes bdd (Suc (Suc dn)))" rule: nat_2_case)
			apply simp
			apply simp
			using abdd_linear_3_eq goal(2) le(2) by blast
	next
		have 1: "abdd_linear bdd \<and> right (nodes bdd (Suc (Suc dn))) < nodecount bdd" using goal(2) by (simp add: le(2))
		case goal2 show ?case (is ?kees)
		proof(cases "2 \<le> right (nodes bdd (Suc (Suc dn)))")
			case True
			have 2: "variable (nodes bdd (right (nodes bdd (Suc (Suc dn))))) < variable (nodes bdd (Suc (Suc dn)))"
				using goal(4) goal(2) goal(3) True
				unfolding abdd_ordered_def Let_def
			proof -
				case goal1
				have "Suc (Suc dn) \<in> {2..<nodecount bdd}" using goal1 by force
				hence "abdd_terminal (right (nodes bdd (Suc (Suc dn)))) \<or> ?case" using goal1(1) by blast
				thus ?case unfolding abdd_terminal_def using goal1(4) by linarith
			qed
			thus ?kees
				by(simp add: le linear_notouch[OF 1 2 goal(4), of as] abdd_linear_3_eq goal1(2))
		next
			case False thus ?kees by(cases rule: nat_2_case_only[OF False]) simp_all
		qed
	qed
qed
(* Todo: Versions of these two proofs with False. Should be C&P. Then maybe even make a version of these for abdd_restrict_top *)

(* Now, let's hack around\<dots> the predecessor of the nodecount is the first node. *)
(* We may want to change that up, i.e. decrease the nodecount by one and adjust all the definitions *)

definition "abdd_restrict_top bdd var val = 
	(let nod = nodes bdd (nat.pred (nodecount bdd)) in if variable nod = var then \<lparr> nodecount = Suc ((if val then right else left) nod), nodes = nodes bdd\<rparr> else bdd)
"
value "(op - 5) 10 :: nat"
definition "abdd_move bdd n = \<lparr> nodecount = nodecount bdd + n, nodes = (\<lambda>nod. 
	let m = (\<lambda>p. if abdd_terminal (p nod) then p nod else p nod + n) in
	\<lparr> variable = variable nod, right = m right, left = m left \<rparr> ) \<circ> nodes bdd \<circ> (\<lambda>x. x - n) \<rparr>"
(* sanity check *)
lemma [simp]: "abdd_move bdd 0 = bdd"
	unfolding abdd_move_def
	unfolding Let_def comp_def
	unfolding add_0_right diff_zero
	unfolding if_cancel
	by(rule abdd.equality) auto

lemma abstract_moved: "2 < k \<Longrightarrow> (nat.pred (nodecount bdd)) = k \<Longrightarrow> abdd_linear bdd \<Longrightarrow>
	(let m = (abdd_move bdd n) in abstract_abdd3 m (nat.pred (nodecount m)) as)	= abstract_abdd3 bdd k as"
unfolding Let_def
proof(induction rule: abstract_abdd3.induct, simp add: abdd_move_def, simp add: abdd_move_def)
	case goal1
	have les: "Suc (Suc dn) < nodecount bdd" by (metis goal1(3) le_less less_eq_Suc_le nat.split_sels(1) nat_neq_iff old.nat.distinct(2) pred_def)
	have bos: "(if as (variable (nodes bdd (Suc (Suc dn)))) then right (nodes bdd (Suc (Suc dn))) else left (nodes bdd (Suc (Suc dn))))
  < Suc (Suc dn)" (is "?mors < _") using abdd_linear_le[OF _ conjI, OF twolesucsuc goal1(4) les] by presburger
	show ?case
		(*unfolding abdd_move_def abdd_terminal_def*)
		unfolding abstract_abdd3.simps
		unfolding abdd.simps comp_def
		unfolding Let_def
		using goal1(1)[of as, OF bos]
sorry (* looks like a lot of fun *)
qed

lemma nat_sel: "nat.pred (Suc x) = x" by simp
(* try this: thm Nat.nat.sel - WTF? *)

lemma abstract_abdd3_inv: "m = \<lparr> nodecount = foo, nodes = n2 \<rparr> \<Longrightarrow> abdd_ordered bdd \<Longrightarrow> \<forall>x \<in> {2..k}. n2 x = nodes bdd x \<Longrightarrow> 
	abstract_abdd3 m k as = abstract_abdd3 bdd k as"
apply(induction rule: abstract_abdd3.induct, simp, simp)
sorry

abbreviation "Suc2 x \<equiv> Suc (Suc x)"
abbreviation "Suc3 x \<equiv> Suc2 (Suc x)" 
definition "abdd_merge T Ebase maxs = (let E = abdd_move Ebase (nodecount T) in \<lparr> nodecount = Suc (nodecount E), nodes = 
					(\<lambda>n. if n = nodecount E then \<lparr> variable = maxs, right = nat.pred (nodecount T), left = nat.pred (nodecount E) \<rparr> 
					else (if n < nodecount T then nodes T n else nodes E n)) \<rparr>)"
lemma abstract_merge: "2 < nodecount T \<Longrightarrow> 2 < nodecount E \<Longrightarrow> abdd_ordered T \<Longrightarrow>
	(let M = (abdd_merge T E var) in abstract_abdd3 M (nat.pred (nodecount M))) as = abstract_abdd3 T (nat.pred (nodecount T)) as"
proof(cases "as var")
	case goal1
	from goal1(1) obtain x where x: "nodecount T = Suc3 x" by (metis add_2_eq_Suc less_imp_Suc_add)
	obtain y where y: "nodecount (abdd_move E (Suc3 x)) = Suc2 y" by (simp add: abdd_move_def)
	have le1: "Suc2 x < Suc2 y" using x y unfolding abdd_move_def abdd.simps using goal1(2) by simp
	have "\<forall>n \<in>{2..Suc2 x}. (if n = Suc2 y then \<lparr>variable = var, right = Suc2 x, left = nat.pred (Suc2 y)\<rparr> 
		else if n < Suc3 x then nodes T n else nodes (abdd_move E (Suc3 x)) n) = nodes T n"
		using le1 by simp
	note hel = abstract_abdd3_inv[OF refl goal1(3) this]
	show ?case
		unfolding abdd_merge_def
		unfolding Let_def
		unfolding abdd.simps
		unfolding x
		unfolding nat_sel
		unfolding y
		unfolding abstract_abdd3.simps
		by(simp only: refl if_True le1 abdd.simps abdd_node.simps goal1(4) hel, simp)
next
	case goal2 thus ?case sorry (* should basically be similar, just that you'd have to unfold abstract_moved *)
qed


fun abdd_ite where "abdd_ite F G H lastmax = (
	let gsv = (\<lambda>d. variable (nodes d (nat.pred (nodecount d))));
	maxs = max (gsv F) (max (gsv G) (gsv H)) in
	if maxs < lastmax then
		(if nodecount F = 1 then
			H
		else if nodecount F = 2 then 
			G
		else 
			let r = (\<lambda>v. abdd_ite (abdd_restrict_top F maxs v) (abdd_restrict_top G maxs v) (abdd_restrict_top H maxs v) maxs);
				T = r True; 
				E = r False in 
				abdd_merge T E maxs 
			)
	else undefined)"
(* Instead of having three bdds, we may instead want to pass around three "pointers" into one bdd.
   This would save us this crazy move function and be a closer to what we actually want to implement.
   (I just lack the creativity of how to do that right now. I have an idea though, ask me if in doubt.)
*)

theorem "abstract_abdd (abdd_ite F G H l) k = bf_ite (abstract_abdd F k) (abstract_abdd G k) (abstract_abdd H k)"
(* 
	Todo: Find meaningful expressions or conditions for k, l and meaningful sanity assumptions 
	And then: Fucking have fun!
*)
sorry

end

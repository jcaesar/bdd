theory AbstractBDD
imports BoolFunc
begin

record abdd_node =
	var :: nat
	right :: nat
	left :: nat
	
record abdd =
	nodecount :: "nat"
	nodes :: "nat \<Rightarrow> abdd_node"

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
		
definition "abdd_terminal state = (state \<le> 1)" 
definition "abdd_xor \<equiv> \<lparr> nodecount = 5, nodes = (\<lambda>i. [undefined, undefined,
	\<lparr> var = 1, right = 1, left = 0 \<rparr>,
	\<lparr> var = 1, right = 0, left = 1 \<rparr>,
	\<lparr> var = 0, right = 3, left = 2 \<rparr>] ! i)
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
	then (\<lambda>as. let nod = nodes bdd n in (if as (var nod) then abstract_abdd bdd (right nod) as else abstract_abdd bdd (left nod) as))
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

(*
definition "abdd_restrict_top bdd val = \<lparr> nodes = nodes bdd, 
	start = ((if val then right else left) \<circ> the \<circ> getnode bdd \<circ> start) bdd  \<rparr>"

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
*)
term "if as (var node) then right (nodes bdd nl) else left (nodes bdd nl)"
definition "abstract_abdd2 bdd start as = 
	(let plain = map (\<lambda>nl. (nl, if as (var (nodes bdd nl)) then right (nodes bdd nl) else left (nodes bdd nl))) (upt 2 (nodecount bdd)); tc = {(0,0),(1,1)} \<union> trancl (set plain) in
	case ((start, 1) \<in> tc, (start, 0) \<in> tc) of
		(True, False) \<Rightarrow> True |
		(False, True) \<Rightarrow> False |
		_ \<Rightarrow> False)" (* miraculously more helpful than undefined *)

value "map (abstract_abdd2 abdd_xor (nodecount abdd_xor - 1)) 
	[(\<lambda>i. [False, False] ! i), (\<lambda>i. [False, True] ! i), (\<lambda>i. [True, False] ! i), (\<lambda>i. [True, True] ! i)]" (* meh. :( *)
value "(\<lambda>bdd start as. let plain = map (\<lambda>nl. (nl, if as (var (nodes bdd nl)) then right (nodes bdd nl) else left (nodes bdd nl))) (upt 2 (nodecount bdd));
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
	let ?foo = "{(0, 0), (1, 1)} \<union> (set (map (\<lambda>nl. (nl, if as (var (nodes bdd nl)) then right (nodes bdd nl) else left (nodes bdd nl))) [2..<nodecount bdd]))\<^sup>+"
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
	show "\<not>abstract_abdd2 bdd 0 as" "abstract_abdd2 bdd 1 as" unfolding abstract_abdd2_def Let_def  using 3 4 5 by simp_all
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

lemma abstract_abdd2_istep_right: "as (var (nodes bdd (Suc (Suc dn)))) \<Longrightarrow> Suc (Suc dn) < nodecount bdd \<Longrightarrow>
	abstract_abdd2 bdd (Suc (Suc dn)) as = abstract_abdd2 bdd (right (nodes bdd (Suc (Suc dn)))) as"
proof -
	let ?x = "Suc (Suc dn)"
	let ?bs = "set (map (\<lambda>nl. (nl, if as (var (nodes bdd nl)) 
	then right (nodes bdd nl) else left (nodes bdd nl))) [2..<nodecount bdd])"
	let ?mors = "{(0, 0), (1, 1)} \<union> ?bs\<^sup>+"
	note dteam = abstract_abdd2_def Let_def case_defeat
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
			unfolding abstract_abdd2_def Let_def case_defeat
			by(simp only: a b if_True if_False)
	qed
qed

lemma abstract_abdd2_istep_left: "\<not>as (var (nodes bdd (Suc (Suc dn)))) \<Longrightarrow> Suc (Suc dn) < nodecount bdd \<Longrightarrow>
	abstract_abdd2 bdd (Suc (Suc dn)) as = abstract_abdd2 bdd (left (nodes bdd (Suc (Suc dn)))) as"
proof -
	let ?x = "Suc (Suc dn)"
	let ?bs = "set (map (\<lambda>nl. (nl, if as (var (nodes bdd nl)) 
	then right (nodes bdd nl) else left (nodes bdd nl))) [2..<nodecount bdd])"
	let ?mors = "{(0, 0), (1, 1)} \<union> ?bs\<^sup>+"
	note dteam = abstract_abdd2_def Let_def case_defeat
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
		have 1: "(left (nodes bdd (Suc (Suc dn))), 1) \<in> ?mors"
			using goal2 unfolding dteam
			by meson
		have a: "(Suc (Suc dn), 1) \<in> ?mors" 
			using pe 1
			by(cases "left (nodes bdd (Suc (Suc dn))) = 1") simp_all
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
		have b: "(Suc (Suc dn), 0) \<notin> ?mors"
		proof(rule ccontr, unfold not_not)
			case goal1
			then have "(Suc (Suc dn), 0) \<in> ?bs\<^sup>+" by force
			with pe have "(left (nodes bdd (Suc (Suc dn))), 0) \<in> ?mors" by (simp add: 4 i trancl_onepath)
			with 3 show False ..
		qed
		show ?case
			unfolding abstract_abdd2_def Let_def case_defeat
			by(simp only: a b if_True if_False)
	qed
qed

lemma "abdd_linear bdd \<and> start < nodecount bdd \<Longrightarrow> abstract_abdd bdd start as = abstract_abdd2 bdd start as"
proof(induction rule: abstract_abdd.induct, simp add: abstract_abdd_eq_hlp1(1))
	case goal1 show ?case using abstract_abdd_eq_hlp1(2) by auto (* try simp. weird. *)
next
	case goal2
	have "right (nodes bdd (Suc (Suc dn))) < (Suc (Suc dn))" using goal2(3) unfolding abdd_linear_def Let_def by force
	then have 1: "abdd_linear bdd \<and> right (nodes bdd (Suc (Suc dn))) < nodecount bdd" using goal2(3) by linarith
	have "left (nodes bdd (Suc (Suc dn))) < (Suc (Suc dn))" using goal2(3) unfolding abdd_linear_def Let_def by force
	then have 2: "abdd_linear bdd \<and> left (nodes bdd (Suc (Suc dn))) < nodecount bdd" using goal2(3) by linarith
	show ?case (is ?kees)
	proof(cases "as (var (nodes bdd (Suc (Suc dn))))")
		case True
		note k = goal2(1)[OF refl goal2(3) refl _ 1, of as]
		show ?kees  by(simp only: abstract_abdd.simps Let_def goal2(3) simp_thms if_True True k[OF True] abstract_abdd2_istep_right)
	next
		case False
		note k = goal2(2)[OF refl _ refl _ 2, of as]
		show ?kees by(simp only: abstract_abdd.simps Let_def goal2(3) simp_thms if_False if_True False k abstract_abdd2_istep_left)
	qed
qed

end

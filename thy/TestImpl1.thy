theory TestImpl1
imports Abstract_Impl
begin

record bdd = 
	nodes :: "nat \<Rightarrow> (nat \<times> nat \<times> nat)"
	bmax :: nat

fun destrmi :: "nat \<Rightarrow> bdd \<Rightarrow> (nat, nat) IFEXD" where
"destrmi 0 bdd = FD" |
"destrmi (Suc 0) bdd = TD" |
"destrmi n bdd = (case nodes bdd n of (v, t, e) \<Rightarrow> IFD v t e)"

fun tmi where "tmi bdd = (1, \<lparr>nodes = nodes bdd, bmax = max 2 (bmax bdd)\<rparr>)"
fun fmi where "fmi bdd = (0, \<lparr>nodes = nodes bdd, bmax = max 2 (bmax bdd)\<rparr>)"
fun ifmi :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bdd \<Rightarrow> (nat \<times> bdd)" where
"ifmi v t e bdd = 
(case List.find (\<lambda>(_,(n,_,_)). v = n) (map (\<lambda>i. (i, nodes bdd i)) (upt 2 (bmax bdd))) of 
	Some (i,_) \<Rightarrow> (i, bdd) |
	None \<Rightarrow> (bmax bdd, \<lparr>nodes = (nodes bdd)(bmax bdd := (v,t,e)), bmax = Suc (bmax bdd)\<rparr>))"

fun Rmi_g :: "nat \<Rightarrow> nat ifex \<Rightarrow> bdd \<Rightarrow> bool" where
"Rmi_g 0 Falseif _ = True" |
"Rmi_g (Suc 0) Trueif _ = True" |
"Rmi_g n (IF v t e) bdd = (if bmax bdd \<le> n \<or> n \<le> 1 then False else case nodes bdd n of (nv, nt, ne) \<Rightarrow> nv = v \<and> Rmi_g nt t bdd \<and> Rmi_g ne e bdd)" |
"Rmi_g _ _ _ = False"

definition "lesmi s s' \<equiv> (\<forall>i \<in> {0..<bmax s}. nodes s i = nodes s' i) \<and> bmax s \<le> bmax s'"

lemma Rmi_gI: "lesmi s s' \<Longrightarrow> Rmi_g n bdd s \<Longrightarrow> Rmi_g n bdd s'"
	by(induction n bdd s' rule: Rmi_g.induct) (auto simp add: lesmi_def split: if_splits)

lemma prod_split3: "P (case prod of (x, xa, xaa) \<Rightarrow> f x xa xaa) = (\<forall>x1 x2 x3. prod = (x1, x2, x3) \<longrightarrow> P (f x1 x2 x3))"
by(simp split: prod.splits)

lemma rmigif: "Rmi_g ni (IF v n1 n2) s \<Longrightarrow> \<exists>n. ni = Suc (Suc n)"
apply(cases ni)
apply(simp split: if_splits prod.splits)
apply(case_tac nat)
apply(simp split: if_splits prod.splits)
apply(simp split: if_splits prod.splits)
done

interpretation brofix!: bdd_impl "(\<lambda>s. {(a,b). Rmi_g a b s})" tmi fmi ifmi destrmi lesmi
unfolding comp_def const_def
proof -
	fix s s'
	have "lesmi s s' =  (\<forall>ni n. (ni, n) \<in> {(a, b). Rmi_g a b s} \<longrightarrow> (ni, n) \<in> {(a, b). Rmi_g a b s'})" 
	proof
		case goal1
		{
			fix n ni
			from goal1 have "Rmi_g ni n s \<Longrightarrow> Rmi_g ni n s'"
			by(induction ni n s' arbitrary: s rule: Rmi_g.induct)
			  (auto simp add: lesmi_def split: prod.splits if_splits)
		}
		thus ?case by simp
	next
		case goal2 thus ?case sorry
	qed
	thus "lesmi s s' \<equiv>  (\<forall>ni n. (ni, n) \<in> {(a, b). Rmi_g a b s} \<longrightarrow> (ni, n) \<in> {(a, b). Rmi_g a b s'})" by presburger
next
	show "bdd_impl (\<lambda>s. {(a, b). Rmi_g a b s}) tmi fmi ifmi destrmi"
	proof(unfold_locales)
	     case goal1 thus ?case by(auto intro: Rmi_gI[unfolded lesmi_def])
	next case goal2 thus ?case by(auto intro: Rmi_gI[unfolded lesmi_def])
	next case goal3 thus ?case by(auto intro: Rmi_gI[unfolded lesmi_def] split: prod.splits option.splits)
	next case goal4 thus ?case by(auto)
	next case goal5 thus ?case by(simp)
	next
		case goal6 
		from goal6 have "Rmi_g ni (IF v n1 n2) s'" apply(clarsimp simp only: ifmi.simps prod.simps find_Some_iff split: option.splits prod.splits)
		apply(simp only: Rmi_g.simps bdd.simps Suc_n_not_le_n  split: if_splits)
		thus ?case apply(clarsimp split: option.splits prod.splits) apply(rule) 
		sorry
		by(auto intro: Rmi_gI[unfolded lesmi_def])
	next
		case goal7 thus ?case apply(simp) apply(cases ni, simp) apply(case_tac nat, simp) apply simp done
	next
		case goal8 thus ?case apply(cases ni, simp) apply simp done
	next
		case goal9 thus ?case 
			apply clarify
			apply(frule rmigif, clarify)
			apply(simp add: rmigif split: if_splits prod.splits)
		done
	qed
qed

end
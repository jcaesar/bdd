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
(case List.find (\<lambda>(_,tup). (v,t,e) = tup) (map (\<lambda>i. (i, nodes bdd i)) (upt 2 (bmax bdd))) of 
	Some (i,_) \<Rightarrow> (i, bdd) |
	None \<Rightarrow> (bmax bdd, \<lparr>nodes = (nodes bdd)(bmax bdd := (v,t,e)), bmax = Suc (bmax bdd)\<rparr>))"

fun Rmi_g :: "nat \<Rightarrow> nat ifex \<Rightarrow> bdd \<Rightarrow> bool" where
"Rmi_g 0 Falseif bdd = (2 \<le> bmax bdd)" | (* needs to be 2 and not 1. This is where the 1 is hardcoded Trueif is ensured for arbitrarily constructed bdds *)
"Rmi_g (Suc 0) Trueif bdd = (2 \<le> bmax bdd)" |
"Rmi_g n (IF v t e) bdd = (if 2 \<le> n \<and> n < bmax bdd then (case nodes bdd n of (nv, nt, ne) \<Rightarrow> nv = v \<and> Rmi_g nt t bdd \<and> Rmi_g ne e bdd) else False)" |
"Rmi_g _ _ _ = False"

definition "lesmi s s' \<equiv> (\<forall>ni n. (ni, n) \<in> {(a, b). Rmi_g a b s} \<longrightarrow> (ni, n) \<in> {(a, b). Rmi_g a b s'})"

lemma prod_split3: "P (case prod of (x, xa, xaa) \<Rightarrow> f x xa xaa) = (\<forall>x1 x2 x3. prod = (x1, x2, x3) \<longrightarrow> P (f x1 x2 x3))"
by(simp split: prod.splits)

lemma rmigif: "Rmi_g ni (IF v n1 n2) s \<Longrightarrow> \<exists>n. ni = Suc (Suc n)"
apply(cases ni)
apply(simp split: if_splits prod.splits)
apply(case_tac nat)
apply(simp split: if_splits prod.splits)
apply(simp split: if_splits prod.splits)
done
lemma rmig2: "Rmi_g ni n s \<Longrightarrow> 2 \<le> (bmax s)"
by(cases "(ni,n,s)" rule: Rmi_g.cases) (simp_all split: if_splits)

lemma IfI: "(c \<Longrightarrow> P x) \<Longrightarrow> (\<not>c \<Longrightarrow> P y) \<Longrightarrow> P (if c then x else y)" by simp

lemma rmi_appendD1: "Rmi_g ni1 n1 s \<Longrightarrow> Rmi_g ni1 n1 \<lparr>nodes = (nodes s), bmax = Suc (bmax s)\<rparr>"
by(induction ni1 n1 s rule: Rmi_g.induct) (simp_all split: if_splits prod.splits)
lemma rmi_appendD2: "Rmi_g ni1 n1 s \<Longrightarrow> Rmi_g ni1 n1 \<lparr>nodes = (nodes s)(bmax s := x), bmax = bmax s\<rparr>"
by(induction ni1 n1 s rule: Rmi_g.induct) (simp_all split: if_splits prod.splits)

lemma rmi_appendD: "Rmi_g ni1 n1 s \<Longrightarrow> Rmi_g ni2 n2 s \<Longrightarrow> Rmi_g ni1 n1 \<lparr>nodes = (nodes s)(bmax s := (v, ni1, ni2)), bmax = Suc (bmax s)\<rparr>"
apply(cases "(ni1,n1,s)" rule: Rmi_g.cases)
apply(simp_all)[2]
apply(clarsimp simp only: prod.simps)
apply(subst Rmi_g.simps)
apply(rule IfI)
apply(clarsimp split: prod.splits)
apply(metis not_less_iff_gr_or_eq rmi_appendD1 rmi_appendD2 select_convs(1,2))
apply(auto)
done

interpretation brofix!: bdd_impl "(\<lambda>s. {(a,b). Rmi_g a b s})" tmi fmi ifmi destrmi lesmi
unfolding comp_def const_def
proof -
	fix s s'
	have "lesmi s s' =  (\<forall>ni n. (ni, n) \<in> {(a, b). Rmi_g a b s} \<longrightarrow> (ni, n) \<in> {(a, b). Rmi_g a b s'})"
	unfolding lesmi_def ..
	thus "lesmi s s' \<equiv>  (\<forall>ni n. (ni, n) \<in> {(a, b). Rmi_g a b s} \<longrightarrow> (ni, n) \<in> {(a, b). Rmi_g a b s'})" by presburger
next
	show "bdd_impl (\<lambda>s. {(a, b). Rmi_g a b s}) tmi fmi ifmi destrmi"
	proof(unfold_locales)
	     case goal1 thus ?case by(clarsimp, metis (mono_tags, lifting) max_def old.unit.exhaust rmig2 surjective)
	next case goal2 thus ?case by(clarsimp, metis (mono_tags, lifting) max_def old.unit.exhaust rmig2 surjective)
	next case goal3 thus ?case
	apply(case_tac "List.find (\<lambda>(_, y). (v, ni1, ni2) = y) (map (\<lambda>i. (i, nodes s i)) [2..<bmax s])")
	apply(simp_all split: prod.splits)
	 apply(clarsimp split: option.split prod.split)
	 	using rmi_appendD1 rmi_appendD2 by fastforce
	next case goal4 thus ?case by(auto)
	next case goal5 thus ?case by(auto)
	next
		case goal6
		from goal6(1,2) have s: "Rmi_g ni1 n1 s" "Rmi_g ni2 n2 s" by simp_all
		from s(1) have g: "2 \<le> bmax s" using rmig2 by simp
		from s goal6(3) have "Rmi_g ni (IF v n1 n2) s'"
		proof(cases "List.find (\<lambda>(_,tup). (v,ni1,ni2) = tup) (map (\<lambda>i. (i, nodes s i)) (upt 2 (bmax s)))")
			case None thus ?thesis using s goal6(3) 
			by(simp_all only: ifmi.simps option.simps split: prod.splits, clarsimp split: prod.splits)
			  (metis g rmi_appendD1 rmi_appendD2 select_convs(1,2))
		next
			case (Some a)
			have seq: "s' = s" using goal6(3) Some by(simp split: prod.splits)
			from Some obtain i tb fb where a: "a = (i, v, tb, fb)" unfolding find_Some_iff by blast
			from Some[unfolded this] have neq: "nodes s i = (v, tb, fb)" 
			unfolding find_Some_iff unfolding length_map length_upt 
			proof(clarify) 
				case goal1 
				note nth_map_upt[OF goal1(1)]
				note goal1(3)[unfolded this]
				thus ?case by auto
			qed
			from goal6(3)[symmetric, unfolded ifmi.simps] have ieq: "ni = i" by(simp only: Some option.simps a, simp)
			have ic: "2 \<le> ni \<and> ni < bmax s'" using Some goal6(3) apply(simp add: ieq seq split: prod.splits) 
			unfolding find_Some_iff unfolding length_map length_upt using nth_map_upt by auto
			have soeq: "ni1 = tb" "ni2 = fb" 
				using neq a goal6(3) Some apply(simp only: ifmi.simps option.simps prod.simps split: prod.splits) apply (metis (mono_tags, lifting) Pair_inject find_Some_iff splitD)
				using neq a goal6(3) Some apply(simp only: ifmi.simps option.simps prod.simps split: prod.splits) apply (metis (mono_tags, lifting) Pair_inject find_Some_iff splitD)
				done
			show ?thesis apply(simp only: Rmi_g.simps ic simp_thms if_True) apply(simp only: seq ieq neq split: prod.splits) apply(clarify) apply(rule) apply simp apply rule apply(simp_all add: s[unfolded soeq]) done 
		qed
		thus ?case by simp
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
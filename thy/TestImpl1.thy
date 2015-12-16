theory TestImpl1
imports Abstract_Impl
begin

record bdd = 
	nodes :: "(nat \<times> nat \<times> nat) list"
	lunode :: "(nat \<times> nat \<times> nat) \<Rightarrow> nat option"

definition "bdd_valid d \<equiv> (\<forall>i \<in> set (upt 0 (length (nodes d))). lunode d (nodes d ! i) = Some i)" 

fun destrmi :: "nat \<Rightarrow> bdd \<Rightarrow> (nat, nat) IFEXD" where
"destrmi 0 bdd = FD" |
"destrmi (Suc 0) bdd = TD" |
"destrmi n bdd = (case nodes bdd ! n of (v, t, e) \<Rightarrow> IFD v t e)"

definition "defnodes bdd \<equiv> (if length (nodes bdd) < 2 then \<lparr>nodes = [] @ [undefined] @ [undefined], lunode = lunode bdd \<rparr> else bdd)"

fun tmi where "tmi bdd = (1, defnodes bdd)"
fun fmi where "fmi bdd = (0, defnodes bdd)"
fun ifmi :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bdd \<Rightarrow> (nat \<times> bdd)" where
"ifmi v t e bdd = (if t = e then (t, bdd) else 
(case lunode bdd (v, t, e) of
	Some i \<Rightarrow> (i, bdd) |
	None \<Rightarrow> (length (nodes bdd), \<lparr>nodes = (nodes bdd)@[(v,t,e)], lunode = (lunode bdd)((v,t,e) \<mapsto> length (nodes bdd))\<rparr>)))"

fun Rmi_g :: "nat \<Rightarrow> nat ifex \<Rightarrow> bdd \<Rightarrow> bool" where
"Rmi_g 0 Falseif bdd = (2 \<le> length (nodes bdd))" | (* needs to be 2 and not 1. This is where the 1 is hardcoded Trueif is ensured for arbitrarily constructed bdds *)
"Rmi_g (Suc 0) Trueif bdd = (2 \<le> length (nodes bdd))" |
"Rmi_g n (IF v t e) bdd = (if 2 \<le> n \<and> n < length (nodes bdd) then (case nodes bdd ! n of (nv, nt, ne) \<Rightarrow> nv = v \<and> Rmi_g nt t bdd \<and> Rmi_g ne e bdd) else False)" |
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
lemma rmig2: "Rmi_g ni n s \<Longrightarrow> 2 \<le> (length (nodes s))"
by(cases "(ni,n,s)" rule: Rmi_g.cases) (simp_all split: if_splits)
lemma rmig3: "Rmi_g ni n s \<Longrightarrow> ni < (length (nodes s))"
by(cases "(ni,n,s)" rule: Rmi_g.cases) (auto simp add: defnodes_def split: if_splits)

lemma IfI: "(c \<Longrightarrow> P x) \<Longrightarrow> (\<not>c \<Longrightarrow> P y) \<Longrightarrow> P (if c then x else y)" by simp

lemma rmi_appendD: "Rmi_g ni1 n1 s \<Longrightarrow> Rmi_g ni1 n1 \<lparr>nodes = (nodes s)@[(v,t,e)], lunode = (lunode s)((v,t,e) \<mapsto> length (nodes s))\<rparr>"
proof(induction ni1 n1 s rule: Rmi_g.induct)
	case goal3 
	from goal3(3) have m1: "2 \<le> n \<and> n < length (nodes bdd)" by(simp split: if_splits)
	from goal3(3) have m2: "Rmi_g (fst (snd (nodes bdd ! n))) t bdd" "Rmi_g (snd (snd (nodes bdd ! n))) e bdd" by(clarsimp split: if_splits option.splits)+
	note mIH1 = goal3(1,2)[OF m1 pair_collapse pair_collapse]
	note mIH = mIH1(1)[OF m2(1)] mIH1(2)[OF m2(2)]
	thus ?case 
		apply(clarsimp simp add: m1 less_SucI nth_append)
		apply (metis (mono_tags, lifting) Rmi_g.simps(3) goal3(3) splitD)
	done
qed simp_all 

(*
lemma rmi_appendD1: "Rmi_g ni1 n1 s \<Longrightarrow> Rmi_g ni1 n1 s\<lparr>nodes = (nodes s), bmax = Suc (bmax s)\<rparr>"
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
*)

lemma rmigeq: "Rmi_g ni1 n1 s \<Longrightarrow> Rmi_g ni2 n2 s \<Longrightarrow> ni1 = ni2 \<Longrightarrow> n1 = n2"
proof(induction ni1 n1 s arbitrary: n2 ni2 rule: Rmi_g.induct)
	case goal3
	have sn: "2 \<le> n \<and> n < length (nodes bdd)" using goal3(3) by simp presburger
	have sn2: "2 \<le> ni2 \<and> ni2 < length (nodes bdd)" using sn unfolding goal3(5) . 
	note 1 = goal3(1,2)[OF sn pair_collapse pair_collapse]
	have 2: "Rmi_g (fst (snd (nodes bdd ! n))) t bdd" "Rmi_g (snd (snd (nodes bdd ! n))) e bdd" using goal3(3) by(clarsimp simp add: sn)+
	note mIH = 1(1)[OF 2(1)] 1(2)[OF 2(2)]
	obtain v2 t2 e2 where v2: "n2 = IF v2 t2 e2" using Rmi_g.simps(4,6) goal3(3-5) rmigif by(cases n2) blast+
	thus ?case using goal3(3-4) by(clarsimp simp add: sn2 sn v2 goal3(5) mIH)
qed (case_tac n2, simp, clarsimp, clarsimp)+
	



interpretation brofix!: bdd_impl "(\<lambda>s. {(a,b). Rmi_g a b s})" tmi fmi ifmi destrmi
unfolding comp_def const_def
proof  -
  note bdd_impl_pre.les_def[simp] defnodes_def[simp]
	show "bdd_impl (\<lambda>s. {(a, b). Rmi_g a b s}) tmi fmi ifmi destrmi"
	proof(unfold_locales)
	     case goal1 thus ?case using rmig2 by fastforce
	next case goal2 thus ?case using rmig2 by fastforce
	next case goal3 thus ?case
	apply(case_tac "lunode s (v, ni1, ni2)")
	apply(simp_all split: prod.splits if_splits)
	 apply(clarsimp split: option.split prod.split)
	 	using rmi_appendD by fastforce
	next case goal4 thus ?case by(auto)
	next case goal5 thus ?case by(auto)
	next
		case goal6
		from goal6(1,2) have s: "Rmi_g ni1 n1 s" "Rmi_g ni2 n2 s" by simp_all
		from s(1) have g: "2 \<le> length (nodes s)" using rmig2 by simp
		from s goal6(3) have "Rmi_g ni (IF v n1 n2) s'"
		proof(cases "ni1 \<noteq> ni2", cases "lunode s (v, ni1, ni2)")
			case None moreover assume "ni1 \<noteq> ni2" ultimately show ?thesis using s goal6(3)
			by(clarsimp simp add: g rmi_appendD split: prod.splits)
		next
			case (Some a) assume nine: "ni1 \<noteq> ni2"
			have seq: "s' = s" using goal6(3) Some nine by(simp split: prod.splits)
			(*from Some obtain i tb fb where a: "a = (i, v, tb, fb)" unfolding find_Some_iff by blast
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
			show ?thesis apply(simp only: Rmi_g.simps ic simp_thms if_True) apply(simp only: seq ieq neq split: prod.splits) apply(clarify) apply(rule) apply simp apply rule apply(simp_all add: s[unfolded soeq]) done *)
			show ?thesis sorry
		next
			assume a: "\<not>ni1 \<noteq> ni2"
			have b: "n1 = n2" by(rule rmigeq[OF s a[unfolded not_not]])
			have sane: "2 \<le> ni \<and> ni < length (nodes s')" using goal6(3) using s(1) b rmig3[OF s(1)] apply(clarsimp simp add: a split: if_splits) print_theorems  sorry 
			from a show ?thesis using s goal6(3) apply(clarsimp simp only: ifmi.simps not_not refl if_True prod.simps) apply(clarsimp simp only: Rmi_g.simps sane simp_thms if_True split: prod.splits)
			apply(rule) defer apply(rule) sorry
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
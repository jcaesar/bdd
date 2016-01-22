section{*Functional interpretation for the abstract implementation*}
theory AbstractInterpretation
imports Abstract_Impl PointerMap
begin

type_synonym bdd = "(nat \<times> nat \<times> nat) pointermap"

fun destrmi :: "nat \<Rightarrow> bdd \<Rightarrow> (nat, nat) IFEXD" where
"destrmi 0 bdd = FD" |
"destrmi (Suc 0) bdd = TD" |
"destrmi (Suc (Suc n)) bdd = (case pm_pth bdd n of (v, t, e) \<Rightarrow> IFD v t e)"

fun tmi where "tmi bdd = (1, bdd)"
fun fmi where "fmi bdd = (0, bdd)"
fun ifmi :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bdd \<Rightarrow> (nat \<times> bdd)" where
"ifmi v t e bdd = (if t = e then (t, bdd) else apfst (Suc \<circ> Suc) (pointermap_getmk (v, t, e) bdd))"

fun Rmi_g :: "nat \<Rightarrow> nat ifex \<Rightarrow> bdd \<Rightarrow> bool" where
"Rmi_g 0 Falseif bdd = True" |
"Rmi_g (Suc 0) Trueif bdd = True" |
"Rmi_g (Suc (Suc n)) (IF v t e) bdd = (pointermap_p_valid n bdd \<and> (case pm_pth bdd n of (nv, nt, ne) \<Rightarrow> nv = v \<and> Rmi_g nt t bdd \<and> Rmi_g ne e bdd))" |
"Rmi_g _ _ _ = False"

definition "Rmi s \<equiv> {(a,b)|a b. Rmi_g a b s}"

lemma prod_split3: "P (case prod of (x, xa, xaa) \<Rightarrow> f x xa xaa) = (\<forall>x1 x2 x3. prod = (x1, x2, x3) \<longrightarrow> P (f x1 x2 x3))"
by(simp split: prod.splits)

lemma IfI: "(c \<Longrightarrow> P x) \<Longrightarrow> (\<not>c \<Longrightarrow> P y) \<Longrightarrow> P (if c then x else y)" by simp
lemma fstsndI: "x = (a,b) \<Longrightarrow> fst x = a \<and> snd x = b" by simp


(*lemma rmi_appendD: "Rmi_g ni1 n1 s \<Longrightarrow> (v2,t2,e2) \<notin> set (entries s) \<Longrightarrow> Rmi_g ni1 n1 (pointermap_getmk (v2,t2,e2) s)"
proof(induction ni1 n1 s rule: Rmi_g.induct)
	case goal3
	have fprems: "Rmi_g (fst (snd (pm_pth bdd n))) t bdd" "Rmi_g (snd (snd (pm_pth bdd n))) e bdd" using goal3(3) by(simp_all split: prod.splits)
	note mIHp = goal3(1,2)[OF pair_collapse pair_collapse _ goal3(4)]
	note mIH = mIHp(1)[OF fprems(1)] mIHp(2)[OF fprems(2)]
	show ?case using goal3(3,4) by(auto simp add: pm_pth_append intro: pointermap_insert_p_validI mIH dest: fstsndI pointermap_sane_appendD[of bdd "(v2, t2, e2)"])
qed simp_all*)

lemma rmigeq: "Rmi_g ni1 n1 s \<Longrightarrow> Rmi_g ni2 n2 s \<Longrightarrow> ni1 = ni2 \<Longrightarrow> n1 = n2"
proof(induction ni1 n1 s arbitrary: n2 ni2 rule: Rmi_g.induct)
	case goal3 
	note 1 = goal3(1,2)[OF pair_collapse pair_collapse]
	have 2: "Rmi_g (fst (snd (pm_pth bdd n))) t bdd" "Rmi_g (snd (snd (pm_pth bdd n))) e bdd" using goal3(3) by(clarsimp)+
	note mIH = 1(1)[OF 2(1) _ refl] 1(2)[OF 2(2) _ refl]
	obtain v2 t2 e2 where v2: "n2 = IF v2 t2 e2" using Rmi_g.simps(4,6) goal3(3-5) by(cases n2) blast+
	thus ?case using goal3(3-4) by(clarsimp simp add: v2 goal3(5)[symmetric] mIH)
qed (case_tac n2, simp, clarsimp, clarsimp)+

lemma rmigneq: "pointermap_sane s \<Longrightarrow> Rmi_g ni1 n1 s \<Longrightarrow> Rmi_g ni2 n2 s \<Longrightarrow> ni1 \<noteq> ni2 \<Longrightarrow> n1 \<noteq> n2"
proof(induction ni1 n1 s arbitrary: n2 ni2 rule: Rmi_g.induct)
	case goal1 thus ?case by (metis Rmi_g.simps(6) old.nat.exhaust)
next
	case goal2 thus ?case by (metis Rmi_g.simps(4,8) old.nat.exhaust)
next
	case goal3
	note 1 = goal3(1,2)[OF pair_collapse pair_collapse]
	have 2: "Rmi_g (fst (snd (pm_pth bdd n))) t bdd" "Rmi_g (snd (snd (pm_pth bdd n))) e bdd" using goal3(4) by(clarsimp)+
	note mIH = 1(1)[OF goal3(3) 2(1)] 1(2)[OF goal3(3) 2(2)]
	show ?case proof(cases "0 < ni2", case_tac "1 < ni2")
		case False
		hence e: "ni2 = 0" by simp
		with goal3(5) have "n2 = Falseif" using rmigeq by auto (* honestly, I'm puzzled how this works\<dots> *)
		thus ?thesis by simp
	next
		case True moreover assume 3: "\<not> 1 < ni2"
		ultimately have "ni2 = 1" by simp
		with goal3(5) have "n2 = Trueif" using rmigeq by auto
		thus ?thesis by simp
	next
		assume 3: "1 < ni2"
		then obtain ni2s where [simp]: "ni2 = Suc (Suc ni2s)" unfolding One_nat_def using less_imp_Suc_add by blast
		obtain v2 t2 e2 where v2[simp]: "n2 = IF v2 t2 e2" using goal3(5) by(cases "(ni2, n2, bdd)" rule: Rmi_g.cases) clarsimp+
		have 4: "Rmi_g (fst (snd (pm_pth bdd ni2s))) t2 bdd" "Rmi_g (snd (snd (pm_pth bdd ni2s))) e2 bdd" using goal3(5) by clarsimp+
		show ?case unfolding v2
		proof(cases "fst (snd (pm_pth bdd n)) = fst (snd (pm_pth bdd ni2s))",
			case_tac "snd (snd (pm_pth bdd n)) = snd (snd (pm_pth bdd ni2s))",
			case_tac "v = v2")
			have ne: "ni2s \<noteq> n" using goal3(6) by simp
			have ib: "pointermap_p_valid n bdd"  "pointermap_p_valid ni2s bdd" using Rmi_g.simps(3) goal3(4,5) by simp_all
			case goal1
			hence "pm_pth bdd n = pm_pth bdd ni2s" unfolding prod_eq_iff using goal3(4) goal3(5) by auto
			with goal3(3) ne have False using pth_eq_iff_index_eq[OF _ ib] by simp
			thus ?case ..
		qed (simp_all add: mIH(1)[OF 4(1)] mIH(2)[OF 4(2)])
	qed
qed simp_all

lemma "pointermap_sane s \<Longrightarrow> tmi s = (ni, s') \<Longrightarrow> in_rel (Rmi s') ni Trueif" by(clarsimp simp add: Rmi_def split: if_splits) (* these should fall out of the interpretation, no? *)
lemma ifmi_saneI: "pointermap_sane s \<Longrightarrow> ifmi v ni1 ni2 s = (ni, s') \<Longrightarrow> pointermap_sane s'"
	apply(clarsimp simp: comp_def apfst_def map_prod_def split: if_splits option.splits split: prod.splits)
	apply(rule conjunct1[OF pointermap_sane_getmkD, of s "(v, ni1, ni2)" _ s'])
	 apply(simp_all)
done

lemma rmigif: "Rmi_g ni (IF v n1 n2) s \<Longrightarrow> \<exists>n. ni = Suc (Suc n)"
apply(cases ni)
apply(simp split: if_splits prod.splits)
apply(case_tac nat)
apply(simp split: if_splits prod.splits)
apply(simp split: if_splits prod.splits)
done

lemma ifmi_les_hlp: "pointermap_sane s \<Longrightarrow> pointermap_getmk (v, ni1, ni2) s = (x1, s') \<Longrightarrow> Rmi_g nia n s \<Longrightarrow> Rmi_g nia n s'"
proof(induction nia n s rule: Rmi_g.induct)
	case goal3
	obtain x1a x2a where pth[simp]: "pm_pth bdd n = (v, x1a, x2a)" using goal3(5) by force
	have pth'[simp]: "pm_pth s' n = (v, x1a, x2a)" unfolding pth[symmetric] using goal3(4,5) by (meson Rmi_g.simps(3) pointermap_p_pth_inv)
	note mIH = goal3(1,2)[OF pth[symmetric] refl goal3(3,4)]
	from goal3(5) show ?case 
		unfolding Rmi_g.simps
		using pointermap_p_valid_inv[OF _ goal3(4)] mIH
		by(simp split: prod.splits)
qed simp_all
lemma ifmi_les:
    assumes "pointermap_sane s"
    assumes "ifmi v ni1 ni2 s = (ni, s')"
    shows "bdd_impl_pre.les Rmi s s'"
using assms
by(clarsimp simp: comp_def apfst_def map_prod_def bdd_impl_pre.les_def Rmi_def ifmi_les_hlp split: if_splits prod.splits)

lemma in_lesI:
	assumes "bdd_impl_pre.les Rmi s s'"
    assumes "(ni1, n1) \<in> Rmi s"
    assumes "(ni2, n2) \<in> Rmi s"
    shows "(ni1, n1) \<in> Rmi s'" "(ni2, n2) \<in> Rmi s'"
by (meson assms bdd_impl_pre.les_def)+

interpretation brofix!: bdd_impl pointermap_sane Rmi tmi fmi ifmi destrmi
proof  -
  note s = bdd_impl_pre.les_def[simp] Rmi_def[simp]
	show "bdd_impl pointermap_sane Rmi tmi fmi ifmi destrmi"
	proof(unfold_locales)
	     case goal1 thus ?case by(clarsimp split: if_splits)
	next case goal2 thus ?case by(clarsimp split: if_splits)
	next case goal3 thus ?case using ifmi_les by blast
	next case goal4 thus ?case by(clarsimp simp add: const_def split: if_splits)
	next case goal5 thus ?case by(clarsimp simp add: const_def split: if_splits)
	next
		case goal6
		from goal6 have s: "Rmi_g ni1 n1 s" "Rmi_g ni2 n2 s" by simp_all
		have sn: "pointermap_sane s" using goal6(1) by simp
		note lesI = ifmi_les[OF `pointermap_sane s`  `ifmi v ni1 ni2 s = (ni, s')`]
		from s goal6(3) have "Rmi_g ni (IFC v n1 n2) s'"
		proof(cases "ni1 = ni2")
			case False 
			have nay: "n1 \<noteq> n2" by
				(rule rmigneq)
				(rule sn,
				 rule s(1),
				 rule s(2),
				 rule False)
			from False show ?thesis
			using `ifmi v ni1 ni2 s = (ni, s')`[unfolded ifmi.simps]
			apply(clarsimp simp: IFC_def nay apfst_def map_prod_def split: prod.splits)
			using s in_lesI[OF lesI] pointermap_update_pthI[OF `pointermap_sane s`] pointermap_sane_getmkD[OF `pointermap_sane s`] apply force
			done
		next
			case True
			have b: "n1 = n2" by(rule rmigeq[OF s True]) 
			from True show ?thesis using s goal6(4) by(clarsimp simp only: ifmi.simps not_not refl if_True prod.simps IFC_def b)
		qed
		with ifmi_saneI[OF sn goal6(4)] show ?case by simp
	next
		case goal7 thus ?case apply(simp) apply(cases ni, simp) apply(case_tac nat, simp) apply simp done
	next
		case goal8 thus ?case apply(cases ni, simp) apply simp done
	next
		case goal9 thus ?case
			apply(unfold Rmi_def)
			apply clarify
			apply(frule rmigif, clarify)
			apply(clarsimp split: prod.splits)
		done
	next
		case goal12 thus ?case using ifmi_saneI by blast
	qed(simp_all)
qed


end

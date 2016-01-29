section{*Functional interpretation for the abstract implementation*}
theory AbstractInterpretation
imports Abstract_Impl PointerMap
begin

type_synonym bdd = "(nat \<times> nat \<times> nat) pointermap"

fun destrmi :: "nat \<Rightarrow> bdd \<Rightarrow> (nat, nat) IFEXD" where
"destrmi 0 bdd = FD" |
"destrmi (Suc 0) bdd = TD" |
"destrmi (Suc (Suc n)) bdd = (case pm_pth bdd n of (v, t, e) \<Rightarrow> IFD v t e)"

definition "bdd_node_valid bdd n \<equiv> n < 2 \<or> pointermap_p_valid (n - 2) bdd"
lemma [simp]: 
  "bdd_node_valid bdd 0"
  "bdd_node_valid bdd (Suc 0)"
  by (auto simp: bdd_node_valid_def)
  
definition "ifexd_valid bdd e \<equiv> (case e of IFD _ t e \<Rightarrow> bdd_node_valid bdd t \<and> bdd_node_valid bdd e | _ \<Rightarrow> True)"
definition "bdd_sane bdd \<equiv> pointermap_sane bdd \<and> (\<forall>n. bdd_node_valid bdd n \<longrightarrow> ifexd_valid bdd (destrmi n bdd))"

lemma ifexd_validI: 
	assumes sane: "bdd_sane bdd" and valid: "bdd_node_valid bdd n"
	shows "ifexd_valid bdd (destrmi n bdd)" 
proof(cases "destrmi n bdd")
	case (IFD v t e)
	note mp[OF spec[OF conjunct2[OF sane[unfolded bdd_sane_def]]], OF valid]
	thus ?thesis .
qed(simp_all add: ifexd_valid_def)

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


lemma bdd_node_valid_RmiI: "(ni,n)\<in>Rmi bdd \<Longrightarrow> bdd_node_valid bdd ni"
  apply (auto simp: Rmi_def)
  apply (cases "(ni,n,bdd)" rule: Rmi_g.cases; simp)
  apply (auto simp: bdd_node_valid_def)
  done

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

lemma ifmi_valid_set_modification:
	assumes ifm: "ifmi v ni1 ni2 s = (ni, s')"
	assumes ne: "ni1 \<noteq> ni2"
	shows "{n. bdd_node_valid s' n} \<subseteq> insert ni {n. bdd_node_valid s n}"
proof
	case goal1
	hence bv: "bdd_node_valid s' x" by simp
	thus ?case proof(cases "x = ni")
		case True thus ?thesis by simp
	next
		case False thus ?thesis proof(cases "x < 2")
			case True thus ?thesis by(simp add: bdd_node_valid_def)
		next
			case False
			have gni: "2 \<le> ni" using ifm ne by(simp add: apfst_def map_prod_def split: prod.splits)
			have pv: "pointermap_p_valid (x - 2) s'" using bv False unfolding bdd_node_valid_def by simp
			have ne': "ni - 2 \<noteq> x - 2" using `x \<noteq> ni` gni False by simp
			have "pointermap_p_valid (x - 2) s" using ifm ne' 
				by(auto simp add: ne apfst_def map_prod_def split: prod.splits dest: pointermap_backward_valid[OF pv])
			thus ?thesis by(simp add: bdd_node_valid_def)
		qed
	qed
qed

lemma ifmi_saneI2:
	assumes sane: "bdd_sane s"
	assumes valid: "bdd_node_valid s ni1"  "bdd_node_valid s ni2" 
	assumes ifm: "ifmi v ni1 ni2 s = (ni, s')"
	shows "bdd_sane s'"
proof -
	have pms: "pointermap_sane s" using sane[unfolded bdd_sane_def] by simp
	hence pms': "pointermap_sane s'" using ifm ifmi_saneI by blast
	have vp: "\<forall>n. bdd_node_valid s n \<longrightarrow> ifexd_valid s (destrmi n s)" using sane unfolding bdd_sane_def by simp
	have "(\<forall>n. bdd_node_valid s' n \<longrightarrow> ifexd_valid s' (destrmi n s'))"
	proof(cases "ni1 = ni2")
		case True thus ?thesis using vp ifm by simp
	next
		case False
		have "\<forall>n. (n = ni \<or> bdd_node_valid s n) \<longrightarrow> ifexd_valid s' (destrmi n s')"
		proof(clarify)
			fix n
			assume eov: "n = ni \<or> bdd_node_valid s n"
			have gmk: "pointermap_getmk (v, ni1, ni2) s = (ni - 2, s')"
				using ifm by(clarsimp simp: `ni1 \<noteq> ni2` apfst_def map_prod_def split: prod.splits)
			hence dme: "destrmi ni s' = IFD v ni1 ni2"
				using ifm pointermap_update_pthI[OF pms gmk]
				by(cases "(ni, s')" rule: destrmi.cases)
				  (clarsimp simp: `ni1 \<noteq> ni2` apfst_def map_prod_def pointermap_update_pthI[OF pms gmk] split: prod.splits)+
			show "ifexd_valid s' (destrmi n s')"
			proof(cases "n = ni")
				case True
					show "ifexd_valid s' (destrmi n s')" unfolding True
					unfolding dme
					using ifm
					apply(clarsimp simp: False apfst_def map_prod_def ifexd_valid_def split: prod.splits)
					apply(frule pointermap_update_pthI[OF pms])
					apply(rule)
					using valid(1) apply(case_tac "ni1 < 2"; simp add: bdd_node_valid_def pointermap_p_valid_inv;fail)
					using valid(2) apply(case_tac "ni2 < 2"; simp add: bdd_node_valid_def pointermap_p_valid_inv)
				done
			next
				case False
				with eov have nv: "bdd_node_valid s n" by simp
				with vp have dv: "ifexd_valid s (destrmi n s)" by simp
				thus ?thesis proof(cases "(n, s')" rule: destrmi.cases)
					case (3 p bdd)
					with nv have pv: "pointermap_p_valid p s" unfolding bdd_node_valid_def by auto
					note ifm[unfolded ifmi.simps if_not_P[OF `ni1 \<noteq> ni2`] apfst_def map_prod_def comp_def id_def]
					show ?thesis 
						using dv 3 pointermap_p_pth_inv[OF pv gmk] gmk
						apply(clarsimp split: prod.splits)
						apply(clarsimp simp: ifexd_valid_def)
						apply(rename_tac a b)
						apply(rule)
						apply(case_tac "a < 2"; simp add: bdd_node_valid_def pointermap_p_valid_inv; fail)
						apply(case_tac "b < 2"; simp add: bdd_node_valid_def pointermap_p_valid_inv; fail)
					done
				qed (simp_all add: ifexd_valid_def)
			qed
		qed
		with ifmi_valid_set_modification[OF ifm False]
		show ?thesis by blast
	qed
	with pms' show ?thesis unfolding bdd_sane_def by blast
qed

lemma ifmi_modification_validI:
	assumes sane: "bdd_sane s"
	assumes ifm: "ifmi v ni1 ni2 s = (ni, s')"
	shows "\<forall>n. bdd_node_valid s n \<longrightarrow> bdd_node_valid s' n"
proof(cases "ni1 = ni2")
	case True with ifm show ?thesis by simp
next
	case False
	show ?thesis using ifm sane
		apply(clarify)
		apply(rename_tac n)
		apply(case_tac "n < 2")
		apply(simp_all add: False apfst_def map_prod_def bdd_node_valid_def bdd_sane_def pointermap_p_valid_inv split: prod.splits)
	done
qed

lemma ifmi_result_validI:
	assumes sane: "bdd_sane s"
	assumes vld: "bdd_node_valid s ni2"
	assumes ifm: "ifmi v ni1 ni2 s = (ni, s')"
	shows "bdd_node_valid s' ni"
using assms
using pointermap_sane_getmkD by(simp add: apfst_def map_prod_def bdd_node_valid_def bdd_sane_def split: if_splits prod.splits, force)

definition "tmi' s \<equiv> do {oassert (bdd_sane s); Some (tmi s)}"
definition "fmi' s \<equiv> do {oassert (bdd_sane s); Some (fmi s)}"
definition "ifmi' v ni1 ni2 s \<equiv> do {oassert (bdd_sane s \<and> bdd_node_valid s ni1 \<and> bdd_node_valid s ni2); Some (ifmi v ni1 ni2 s)}"

definition "destrmi' ni s \<equiv> do {oassert (bdd_sane s \<and> bdd_node_valid s ni); Some (destrmi ni s)}"

lemma Rmi_sv: 
  assumes "bdd_sane s" "(ni,n) \<in> Rmi s" "(ni',n') \<in> Rmi s"  
  shows "ni=ni' \<Longrightarrow> n=n'"
  and "ni\<noteq>ni' \<Longrightarrow> n\<noteq>n'"
  using assms
  apply safe
  apply (simp_all add: Rmi_def)
  using rmigeq apply simp
  apply (clarsimp simp: bdd_sane_def)
  apply (drule (3) rmigneq)
  by simp

lemma True_rep[simp]: "bdd_sane s \<Longrightarrow> (ni,Trueif)\<in>Rmi s \<longleftrightarrow> ni=Suc 0"
  using Rmi_def Rmi_g.simps(2) Rmi_sv(2) by blast

lemma False_rep[simp]: "bdd_sane s \<Longrightarrow> (ni,Falseif)\<in>Rmi s \<longleftrightarrow> ni=0"
  using Rmi_def Rmi_g.simps(1) Rmi_sv(2) by blast


interpretation brofix!: bdd_impl_eq bdd_sane Rmi tmi' fmi' ifmi' destrmi'
proof  -
  note s = bdd_impl_pre.les_def[simp] Rmi_def

  note [simp] = tmi'_def fmi'_def ifmi'_def destrmi'_def

	show "bdd_impl_eq bdd_sane Rmi tmi' fmi' ifmi' destrmi'"
	proof(unfold_locales)
	     case goal1 thus ?case by(clarsimp split: if_splits simp: Rmi_def)
	next case goal2 thus ?case by(clarsimp split: if_splits simp: Rmi_def)
	next case goal3 
	  note [simp] = Rmi_sv[OF this]

	from goal3 show ?case
	  apply -
	  (* TODO/FIXME: Die HilfsLemma, die hier benutzt werden, gehen quer durch verschiedene
	    Ebenen: Mal hat man Rmi, mal Rmi_g, mal ifmi, mal ist ifmi ausgefaltet, usw.! *)
	  apply (auto simp: IFC_def split: Option.bind_split intro: bdd_node_valid_RmiI)
  	apply (clarsimp simp: apfst_def map_prod_def Rmi_def IFC_def split: prod.splits)
  	apply (metis bdd_sane_def ifmi_les_hlp pointermap_sane_getmkD pointermap_update_pthI prod.sel(2) swap_simp)  
  	apply (clarsimp simp: apfst_def map_prod_def Rmi_def IFC_def split: prod.splits)
  	apply (metis apfst_conv ifmi.elims ifmi_saneI2)
  	apply (clarsimp simp: apfst_def map_prod_def Rmi_def IFC_def split: prod.splits)
  	apply (clarsimp simp: bdd_sane_def ifmi_les_hlp)
  	done
	next case goal4 thus ?case 
	  apply (clarsimp simp add: const_def split: Option.bind_splits if_splits)
	  done
	next case goal5 thus ?case by(clarsimp simp add: const_def split: if_splits)
	next case goal6 thus ?case 
	  apply (clarsimp simp add: const_def bdd_node_valid_RmiI split: Option.bind_splits if_splits)
	  apply (auto simp: Rmi_def elim: Rmi_g.elims)
	  done
	next
    case goal7 from Rmi_sv[OF this] show ?case by auto  
	next
    case goal8 from Rmi_sv[OF this] show ?case by auto  
  qed  
qed

end

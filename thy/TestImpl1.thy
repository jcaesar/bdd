theory TestImpl1
imports Abstract_Impl
begin

record bdd = 
	nodes :: "(nat \<times> nat \<times> nat) list"
	lunode :: "(nat \<times> nat \<times> nat) \<Rightarrow> nat option"

definition "sane bdd \<equiv> (distinct (nodes bdd) \<and> (\<forall>n \<in> {..<length (nodes bdd)}. lunode bdd (nodes bdd ! n) = Some n) \<and> (\<forall>p i. lunode bdd p = Some i \<longrightarrow> nodes bdd ! i = p \<and> i < length (nodes bdd)))"

definition "defnodes bdd \<equiv> (if sane bdd then bdd else \<lparr>nodes = [], lunode = const None \<rparr>)"

fun destrmi :: "nat \<Rightarrow> bdd \<Rightarrow> (nat, nat) IFEXD" where
"destrmi 0 bdd = FD" |
"destrmi (Suc 0) bdd = TD" |
"destrmi (Suc (Suc n)) bdd = (case nodes bdd ! n of (v, t, e) \<Rightarrow> IFD v t e)"

fun tmi where "tmi bdd = (1, defnodes bdd)"
fun fmi where "fmi bdd = (0, defnodes bdd)"
fun ifmi :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bdd \<Rightarrow> (nat \<times> bdd)" where
"ifmi v t e bdd = (if t = e then (t, bdd) else 
(case lunode bdd (v, t, e) of
	Some i \<Rightarrow> (Suc (Suc i), bdd) |
	None \<Rightarrow> (Suc (Suc (length (nodes bdd))), \<lparr>nodes = (nodes bdd)@[(v,t,e)], lunode = (lunode bdd)((v,t,e) \<mapsto> length (nodes bdd))\<rparr>)))"

fun Rmi_g :: "nat \<Rightarrow> nat ifex \<Rightarrow> bdd \<Rightarrow> bool" where
"Rmi_g 0 Falseif bdd = True" |
"Rmi_g (Suc 0) Trueif bdd = True" |
"Rmi_g (Suc (Suc n)) (IF v t e) bdd = (n < length (nodes bdd) \<and> (case nodes bdd ! n of (nv, nt, ne) \<Rightarrow> nv = v \<and> Rmi_g nt t bdd \<and> Rmi_g ne e bdd))" |
"Rmi_g _ _ _ = False"

definition "Rmi s \<equiv> {(a,b)|a b. Rmi_g a b s \<and> sane s}"

lemma prod_split3: "P (case prod of (x, xa, xaa) \<Rightarrow> f x xa xaa) = (\<forall>x1 x2 x3. prod = (x1, x2, x3) \<longrightarrow> P (f x1 x2 x3))"
by(simp split: prod.splits)

lemma IfI: "(c \<Longrightarrow> P x) \<Longrightarrow> (\<not>c \<Longrightarrow> P y) \<Longrightarrow> P (if c then x else y)" by simp
lemma fstsndI: "x = (a,b) \<Longrightarrow> fst x = a \<and> snd x = b" by simp

lemma conjI2: "P \<Longrightarrow> Q \<Longrightarrow> Q \<and> P" ..

lemma sane_appendD: "sane s \<Longrightarrow> (v2,t2,e2) \<notin> set (nodes s) \<Longrightarrow> sane \<lparr>nodes = (nodes s)@[(v2,t2,e2)], lunode = (lunode s)((v2,t2,e2) \<mapsto> length (nodes s))\<rparr>"
unfolding sane_def
proof(rule conjI2, rule conjI2)
	case goal3 thus ?case by simp
next
	case goal2 thus ?case 
	apply(unfold Ball_def) 
	apply(rule)
	apply(rule)
	apply(rename_tac n)
	apply(case_tac "n < length (nodes s)")
	proof -
		case goal1 
		from goal1(4) have sa: "\<And>a. (nodes s @ a) ! n = nodes s ! n" by (simp add: nth_append)
		from goal1(1,4) have ih: "lunode s (nodes s ! n) = Some n" by simp
		from goal1(2,4) have ne: "nodes s ! n \<noteq> (v2, t2, e2)" using nth_mem by fastforce
		from sa ih ne show ?case by simp
	next
		case goal2
		from goal2(3,4) have ln: "n = length (nodes s)" by simp
		hence sa: "\<And>a. (nodes s @ [a]) ! n = a" by simp
		from sa ln show ?case by simp
	qed
next
	case goal1 thus ?case
		apply(unfold Ball_def)
		apply(rule)
		apply(auto simp add: nth_append fun_upd_same)
	done
qed

lemma lunodes_noneD: "lunode s (v, ni1, ni2) = None \<Longrightarrow> sane s \<Longrightarrow> (v, ni1, ni2) \<notin> set (nodes s)"
unfolding sane_def
proof
	case goal1
	from goal1(3) obtain n where "n < length (nodes s)" "nodes s ! n = (v, ni1, ni2)" unfolding in_set_conv_nth by blast
	with goal1(2,1) show False by force
qed

lemma rmi_appendD: "Rmi_g ni1 n1 s \<Longrightarrow> (v2,t2,e2) \<notin> set (nodes s) \<Longrightarrow> Rmi_g ni1 n1 \<lparr>nodes = (nodes s)@[(v2,t2,e2)], lunode = (lunode s)((v2,t2,e2) \<mapsto> length (nodes s))\<rparr>"
proof(induction ni1 n1 s rule: Rmi_g.induct)
	case goal3
	have fprems: "Rmi_g (fst (snd (nodes bdd ! n))) t bdd" "Rmi_g (snd (snd (nodes bdd ! n))) e bdd" using goal3(3) by force+
	note mIHp = goal3(1,2)[OF pair_collapse pair_collapse _ goal3(4)]
	note mIH = mIHp(1)[OF fprems(1)] mIHp(2)[OF fprems(2)]
	have ma: "(nodes bdd @ [(v2, t2, e2)]) ! n = nodes bdd ! n" by (meson Rmi_g.simps(3) goal3(3) nth_append)
	show ?case using goal3(3,4) by(auto simp add: ma intro: mIH dest: fstsndI sane_appendD[of bdd v2 t2 e2])
qed simp_all

lemma rmigeq: "Rmi_g ni1 n1 s \<Longrightarrow> Rmi_g ni2 n2 s \<Longrightarrow> ni1 = ni2 \<Longrightarrow> n1 = n2"
proof(induction ni1 n1 s arbitrary: n2 ni2 rule: Rmi_g.induct)
	case goal3 
	note 1 = goal3(1,2)[OF pair_collapse pair_collapse]
	have 2: "Rmi_g (fst (snd (nodes bdd ! n))) t bdd" "Rmi_g (snd (snd (nodes bdd ! n))) e bdd" using goal3(3) by(clarsimp)+
	note mIH = 1(1)[OF 2(1) _ refl] 1(2)[OF 2(2) _ refl]
	obtain v2 t2 e2 where v2: "n2 = IF v2 t2 e2" using Rmi_g.simps(4,6) goal3(3-5) by(cases n2) blast+
	thus ?case using goal3(3-4) by(clarsimp simp add: v2 goal3(5)[symmetric] mIH)
qed (case_tac n2, simp, clarsimp, clarsimp)+

lemma rmigneq: "sane s \<Longrightarrow> Rmi_g ni1 n1 s \<Longrightarrow> Rmi_g ni2 n2 s \<Longrightarrow> ni1 \<noteq> ni2 \<Longrightarrow> n1 \<noteq> n2"
proof(induction ni1 n1 s arbitrary: n2 ni2 rule: Rmi_g.induct)
	case goal1 thus ?case by (metis Rmi_g.simps(6) old.nat.exhaust)
next
	case goal2 thus ?case by (metis Rmi_g.simps(4,8) old.nat.exhaust)
next
	case goal3
	note 1 = goal3(1,2)[OF pair_collapse pair_collapse]
	have 2: "Rmi_g (fst (snd (nodes bdd ! n))) t bdd" "Rmi_g (snd (snd (nodes bdd ! n))) e bdd" using goal3(4) by(clarsimp)+
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
		have 4: "Rmi_g (fst (snd (nodes bdd ! ni2s))) t2 bdd" "Rmi_g (snd (snd (nodes bdd ! ni2s))) e2 bdd" using goal3(5) by clarsimp+
		show ?case unfolding v2
		proof(cases "fst (snd (nodes bdd ! n)) = fst (snd (nodes bdd ! ni2s))",
			case_tac "snd (snd (nodes bdd ! n)) = snd (snd (nodes bdd ! ni2s))",
			case_tac "v = v2")
			have ne: "ni2s \<noteq> n" using goal3(6) by simp
			have ib: "n < length (nodes bdd)"  "ni2s < length (nodes bdd)" using Rmi_g.simps(3) goal3(4,5) by simp_all
			case goal1
			hence "nodes bdd ! n = nodes bdd ! ni2s" unfolding prod_eq_iff using goal3(4) goal3(5) by auto
			with goal3(3) ne have False unfolding sane_def using nth_eq_iff_index_eq[OF _ ib] by simp
			thus ?case ..
		qed (simp_all add: mIH(1)[OF 4(1)] mIH(2)[OF 4(2)])
	qed
qed simp_all

lemma oursolversarestupid: "nodes s = [] \<Longrightarrow> \<lparr>nodes = [], lunode = lunode s\<rparr> = s" by simp

lemma "sane s \<Longrightarrow> tmi s = (ni, s') \<Longrightarrow> in_rel (Rmi s') ni Trueif" by(clarsimp simp add: Rmi_def defnodes_def oursolversarestupid split: if_splits) (* these should fall out of the interpretation, no? *)
lemma ifmi_saneI: "sane s \<Longrightarrow> ifmi v ni1 ni2 s = (ni, s') \<Longrightarrow> sane s'"
by(simp split: if_splits option.splits) (blast dest: lunodes_noneD sane_appendD[of s v ni1 ni2])

lemma rmigif: "Rmi_g ni (IF v n1 n2) s \<Longrightarrow> \<exists>n. ni = Suc (Suc n)"
apply(cases ni)
apply(simp split: if_splits prod.splits)
apply(case_tac nat)
apply(simp split: if_splits prod.splits)
apply(simp split: if_splits prod.splits)
done

interpretation brofix!: bdd_impl Rmi tmi fmi ifmi destrmi
proof  -
  note s = bdd_impl_pre.les_def[simp] defnodes_def[simp] Rmi_def[simp] oursolversarestupid[simp]
	show "bdd_impl Rmi tmi fmi ifmi destrmi"
	proof(unfold_locales)
	     case goal1 thus ?case by(clarsimp split: if_splits)
	next case goal2 thus ?case by(clarsimp split: if_splits)
	next case goal3 thus ?case
		apply(case_tac "lunode s (v, ni1, ni2)") defer
		 apply(simp split: prod.splits if_splits)
		apply(clarsimp split: option.split prod.split)
		apply(cases "ni1 = ni2") apply(simp)
		 apply(simp only: if_False option.simps prod.simps split: option.splits)
		apply(frule sane_appendD[of s v ni1 ni2]) defer
		 apply(fastforce dest: rmi_appendD lunodes_noneD )+
	done
	next case goal4 thus ?case by(clarsimp simp add: sane_def const_def split: if_splits)
	next case goal5 thus ?case by(clarsimp simp add: sane_def const_def split: if_splits)
	next
		case goal6
		from goal6(1,2) have s: "Rmi_g ni1 n1 s" "Rmi_g ni2 n2 s" by simp_all
		have sn: "sane s" using goal6(1) by simp
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
			proof(cases "lunode s (v, ni1, ni2)")
				case None
				have ni: "(v, ni1, ni2) \<notin> set (nodes s)" using sn None by(blast dest: lunodes_noneD)
				show ?thesis using s goal6(3) by(clarsimp simp add: rmi_appendD[OF _ ni] False None nay split: prod.splits ifc_split)
			next
				case (Some a) assume nine: "ni1 \<noteq> ni2"
				have foo: "s' = s" "ni = Suc (Suc a)" using goal6(3) Some nine by(simp_all split: prod.splits)
				have sac: "nodes s ! a = (v, ni1, ni2)" "a < length (nodes s)" using sn[unfolded sane_def] Some by simp_all
				show ?thesis apply(simp add: IFC_def nay foo sac) by(simp only: s simp_thms)
			qed
		next
			case True
			have b: "n1 = n2" by(rule rmigeq[OF s True]) 
			from True show ?thesis using s goal6(3) by(clarsimp simp only: ifmi.simps not_not refl if_True prod.simps IFC_def b)
		qed
		with ifmi_saneI[OF sn goal6(3)] show ?case by simp
	next
		case goal7 thus ?case apply(simp) apply(cases ni, simp) apply(case_tac nat, simp) apply simp done
	next
		case goal8 thus ?case apply(cases ni, simp) apply simp done
	next
		case goal9 thus ?case
			apply(unfold Rmi_def)
			apply clarify
			apply(frule rmigif, clarify)
			apply(clarsimp simp add: rmigif split: if_splits prod.splits)
		done
	qed
qed


end
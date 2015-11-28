theory BDT
imports Boolean_Expression_Checkers
        "../thy/BoolFunc"
begin

(* datatype 'a ifex = Trueif | Falseif | IF 'a "'a ifex" "'a ifex" *)
(* type_synonym boolfunc2 = "(nat \<Rightarrow> bool) \<Rightarrow> bool" *)


fun ifex_variable_set :: "'a ifex \<Rightarrow> 'a set" where
  "ifex_variable_set (IF v t e) = {v} \<union> ifex_variable_set t \<union> ifex_variable_set e" |
  "ifex_variable_set Trueif = {}" |
  "ifex_variable_set Falseif = {}"

fun ordner :: "('a::linorder) ifex \<Rightarrow> bool" where
  "ordner (IF v t e) = ((\<forall>tv \<in> (ifex_variable_set t \<union> ifex_variable_set e). v < tv)
                       \<and> ordner t \<and> ordner e)" |
  "ordner Trueif = True" |
  "ordner Falseif = True"

definition ifex_bf2_rel where
  "ifex_bf2_rel = {(a,b). (\<forall>ass. a ass \<longleftrightarrow> val_ifex b ass) \<and> ordner b}"

(* had we done ifex_variable_list instead of _set, we would have gotten out way easier\<dots> *)
definition "is_lowest_element e S = (e \<in> S \<and> (\<forall>oe \<in> S. e \<le> oe))"
definition select_lowest :: "'a set \<Rightarrow> 'a :: linorder" where "select_lowest a = the_elem {m. m \<in> a \<and> (\<forall>om \<in> a. m \<le> om)}"
lemma select_hlp_ex: "finite (S :: ('a :: linorder) set)  \<Longrightarrow> S \<noteq> {} \<Longrightarrow> \<exists>k. k \<in> {m. m \<in> S \<and> (\<forall>om \<in> S. m \<le> om)}"
using Min.coboundedI Min_in mem_Collect_eq by blast
lemma card2: "2 \<le> card (S :: ('a :: linorder) set) \<Longrightarrow> \<exists>a b. a \<in> S \<and> b \<in> S \<and> a < b"
proof - (* might be more beautifully reprovable under the use of *) thm card_eq_SucD
	assume a: "2 \<le> card S"
	then obtain x where x: "x \<in> S" using card_eq_0_iff by fastforce
	then obtain S' where S': "x \<notin> S'" "S = S' \<union> {x}" using mk_disjoint_insert by force
	with a have "1 \<le> card S'" by (metis One_nat_def Suc_1 Un_insert_right card_infinite card_insert_disjoint finite_Un not_less_eq_eq one_le_numeral sup_bot.right_neutral)
	then obtain y where y: "y \<in> S'" using card_eq_0_iff by fastforce
	then have "x \<noteq> y" "y \<in> S" using S' by blast+
	with x show ?thesis by (meson neq_iff)
qed
lemma select_set_ov: "finite a \<Longrightarrow> (a :: ('a :: linorder) set) \<noteq> {} \<Longrightarrow> card {m. m \<in> a \<and> (\<forall>om \<in> a. m \<le> om)} = 1"
proof(rule ccontr)
	let ?m = "{m \<in> a. \<forall>om\<in>a. m \<le> om}"
	case goal1
	then obtain ae where ae: "ae \<in> a" by blast
	note select_hlp_ex[OF goal1(1)  goal1(2)] then guess k ..
	then have cns: "card ?m \<noteq> 0" using goal1(1) by auto
	moreover have "card ?m < 2"
	proof(rule ccontr)
		case goal1
		obtain a b where ab: "a \<in> ?m" "b \<in> ?m" "a < b" 
		using card2[OF leI[OF goal1]] by blast
		thus False by fastforce
	qed
	ultimately show False using goal1(3) by linarith
qed
lemma select_is_lowest: "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> is_lowest_element (select_lowest S) S"
unfolding is_lowest_element_def
proof -
	case goal1
	note select_set_ov[OF goal1(1) goal1(2)]
	then obtain l where l: "{m \<in> S. \<forall>om\<in>S. m \<le> om} = {l}" by (metis (no_types, lifting) One_nat_def card_eq_SucD)
	thus ?case unfolding select_lowest_def by auto 
qed
lemma finite_ifex_variable_set: "finite (ifex_variable_set k)" by(induction k) simp_all
lemma nonempty_if_variable_set: "ifex_variable_set (IF v t e) \<noteq> {}" by simp
lemma dings_select_helper: "i = (IF iv it ie) \<Longrightarrow> k = (\<Union>(ifex_variable_set ` {i,t,e})) \<Longrightarrow> finite k \<and> k \<noteq> {}"
	using finite_ifex_variable_set nonempty_if_variable_set by auto

fun restrict where
  "restrict (IF v t e) var val = (let rt = restrict t var val; re = restrict e var val in
                   (if v = var then (if val then rt else re) else (IF v rt re)))" |
  "restrict i _ _ = i"

value "ordner (IF 1 Falseif (IF (0::nat) (IF 0 Falseif Falseif) Falseif))"
value "restrict (IF (1::nat) Falseif (IF 0 (IF 0 Falseif Falseif) Falseif)) 1 False"
(* definition "bf2_restrict (i::nat) (val::bool) (func::boolfunc2) \<equiv> (\<lambda>v. func (v(i:=val)))" *)
value "ordner (IF (0::nat) (IF 0 Falseif Falseif) Falseif)"

declare Let_def[simp]

lemma not_element_restrict: "var \<notin> ifex_variable_set (restrict b var val)"
  by (induction b) auto

lemma restrict_assignment: "val_ifex b (ass(var := val)) \<longleftrightarrow> val_ifex (restrict b var val) ass"
  by (induction b) auto

lemma restrict_variables_subset: "ifex_variable_set (restrict b var val) \<subseteq> ifex_variable_set b"
  by (induction b) auto

lemma restrict_ordner_invar: "ordner b \<Longrightarrow> ordner (restrict b var val)"
  using restrict_variables_subset by (induction b) (fastforce)+

lemma restrict_val_invar: "\<forall>ass. a ass = val_ifex b ass \<Longrightarrow> 
      (bf2_restrict var val a) ass = val_ifex (restrict b var val) ass"
  unfolding bf2_restrict_def using restrict_assignment by simp

lemma restrict_ifex_bf2_rel:
"(a, b) \<in> ifex_bf2_rel \<Longrightarrow> (bf2_restrict var val a, restrict b var val) \<in> ifex_bf2_rel"
  unfolding ifex_bf2_rel_def using restrict_ordner_invar restrict_val_invar
  by (clarsimp simp add: bf2_restrict_def restrict_assignment)

function dings :: "'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> ('a :: linorder) ifex" where
  "dings Trueif t e = t" |
  "dings Falseif t e = e" |
  "dings (IF iv it ie) t e = (let i = (IF iv it ie); x = select_lowest (\<Union>(ifex_variable_set ` {i,t,e})) in 
                         (IF x (dings (restrict i x True) (restrict t x True) (restrict e x True))
                               (dings (restrict i x False) (restrict t x False) (restrict e x False))))"
by pat_completeness auto

lemma restrict_size_le: "size (restrict k x val) \<le> size k"
by(induction k) (auto)
lemma restrict_size_less: "x \<in> ifex_variable_set k \<Longrightarrow> size (restrict k x val) < size k"
proof(induction k)
	case (IF v t e)
	thus ?case
	proof(cases "v = x")
		case True
		show ?thesis by(simp only: True restrict.simps refl if_True) (cases val, simp_all add: preorder_class.le_less_trans[OF restrict_size_le])
	next
		case False note of = this
		show ?thesis
		proof(cases "x \<in> ifex_variable_set t")
			case True
			show ?thesis by(simp only: restrict.simps False if_False ifex.size) (simp add: IF.IH(1)[OF True] restrict_size_le add.commute add_le_less_mono)
		next
			case False
			have *: "x \<in> ifex_variable_set e"
			proof(rule ccontr)
				assume "x \<notin> ifex_variable_set e"
				note this False `v \<noteq> x`
				with IF.prems show False by simp
			qed
			show ?thesis by(simp only: restrict.simps of if_False ifex.size) (simp add: IF.IH(2)[OF *] add_mono_thms_linordered_field(4) restrict_size_le)
		qed
	qed
qed simp_all
lemma restrict_size_eqE: "size k = size (restrict k x val) \<Longrightarrow> x \<notin> ifex_variable_set k"
	using less_not_refl restrict_size_less by metis

lemma termlemma2: "xa = select_lowest (\<Union>(ifex_variable_set ` {(IF iv it ie), t, e})) \<Longrightarrow>
       (size (restrict (IF iv it ie) xa val) + size (restrict t xa val) + size (restrict e xa val)) < (size (IF iv it ie) + size t + size e)"
proof(rule ccontr, unfold not_less)
	case goal1 thus ?case
	proof(cases "size (IF iv it ie) + size t + size e < size (restrict (IF iv it ie) xa val) + size (restrict t xa val) + size (restrict e xa val)")
		case False
		with goal1 have *: "size (IF iv it ie) + size t + size e = size (restrict (IF iv it ie) xa val) + size (restrict t xa val) + size (restrict e xa val)" by auto
		have 1: "size (IF iv it ie) = size (restrict (IF iv it ie) xa val)" using restrict_size_le * by (metis False add_less_le_mono order.not_eq_order_implies_strict)
		have 2: "size t = size (restrict t xa val)" using restrict_size_le * by (metis False add.commute add_less_le_mono order.not_eq_order_implies_strict)
		have 3: "size e = size (restrict e xa val)" using * 1 2 by linarith
		note restrict_size_eqE[OF 1] restrict_size_eqE[OF 2] restrict_size_eqE[OF 3]
		then show False unfolding goal1 using dings_select_helper[OF refl refl] 
			conjunct1[OF select_is_lowest[unfolded is_lowest_element_def], of "(\<Union>(ifex_variable_set ` {(IF iv it ie), t, e}))"] by auto 
	next
		case True thus False using restrict_size_le by (metis add_mono_thms_linordered_semiring(1) leD)
	qed
qed
lemma termlemma: "xa = select_lowest (\<Union>(ifex_variable_set ` {(IF iv it ie), t, e})) \<Longrightarrow>
       (case (restrict (IF iv it ie) xa val, restrict t xa val, restrict e xa val) of (i, t, e) \<Rightarrow> size i + size t + size e) < (case (IF iv it ie, t, e) of (i, t, e) \<Rightarrow> size i + size t + size e)"
using termlemma2 by fast
termination dings by(relation "measure (\<lambda>(i,t,e). size i + size t + size e)", rule wf_measure, unfold in_measure) (simp_all only: termlemma)+

definition "const x _ = x" (* Mehr Haskell wagen *)
lemma rel_true_false: "(a, Trueif) \<in> ifex_bf2_rel \<Longrightarrow> a = const True" "(a, Falseif) \<in> ifex_bf2_rel \<Longrightarrow> a = const False"
	unfolding fun_eq_iff const_def
	unfolding ifex_bf2_rel_def 
	by simp_all
lemma rel_if: "(a, IF v t e) \<in> ifex_bf2_rel \<Longrightarrow> (ta, t) \<in> ifex_bf2_rel \<Longrightarrow> (ea, e) \<in> ifex_bf2_rel \<Longrightarrow> a = (\<lambda>as. if as v then ta as else ea as)"
	unfolding fun_eq_iff const_def
	unfolding ifex_bf2_rel_def 
	by simp_all
lemma "as v \<Longrightarrow> (a, (IF v t e)) \<in> ifex_bf2_rel \<Longrightarrow> (bf2_restrict v True a, t) \<in> ifex_bf2_rel"
unfolding in_rel_def[symmetric]
unfolding ifex_bf2_rel_def
unfolding in_rel_Collect_split_eq
unfolding val_ifex.simps
unfolding ordner.simps
unfolding bf2_restrict_def
oops
lemma ifex_bf2_construct: "(ta, tb) \<in> ifex_bf2_rel \<Longrightarrow> (ea, eb) \<in> ifex_bf2_rel \<Longrightarrow> ordner (IF x tb eb) \<Longrightarrow> (\<lambda>as. if as x then ta as else ea as, IF x tb eb) \<in> ifex_bf2_rel"
	unfolding fun_eq_iff const_def
	unfolding ifex_bf2_rel_def
	by simp
	
lemma ordner_implied: "(a, b) \<in> ifex_bf2_rel \<Longrightarrow> ordner b" unfolding ifex_bf2_rel_def by simp

lemma img_three: "foo ` {a, b, c} = {foo a, foo b, foo c}" by simp
lemma Un_three: "\<Union>{a, b, c} = a \<union> b \<union> c" by auto
lemma finite_three: "finite {a, b, c}" by simp

lemma single_valued_rel: "single_valued (ifex_bf2_rel\<inverse>)"
	unfolding single_valued_def
	unfolding ifex_bf2_rel_def
	unfolding converse_unfold
	unfolding in_rel_def[symmetric]  in_rel_Collect_split_eq
	by blast

lemma ifex_variable_set_dings_ss: "ifex_variable_set (dings i t e) \<subseteq> \<Union>(ifex_variable_set ` {i, t, e})"
apply(induction i t e rule: dings.induct)
apply simp_all[2]
apply(subst dings.simps)
apply(unfold Let_def)
apply(subst ifex_variable_set.simps)
apply(rule le_supI)
apply(rule le_supI)
apply rule
apply(unfold singleton_iff)
apply(meson dings_select_helper is_lowest_element_def select_is_lowest)
proof -
	case goal1
	show ?case
		apply(rule subset_trans[OF goal1(1)[OF refl refl]])
		apply(unfold img_three)
		using restrict_variables_subset by fastforce
next
	case goal2
	show ?case
		apply(rule subset_trans[OF goal2(2)[OF refl refl]])
		apply(unfold img_three)
		using restrict_variables_subset by fastforce
qed

lemma Let_keeper: "f (let x = a in b x) = (let x = a in f (b x))" by simp
lemma Let_ander: "(let x = a in b x \<and> c x) = ((let x = a in b x) \<and> (let x = a in c x))" by simp
lemma Let2assm: "(\<And>x. x = foo \<Longrightarrow> f x) \<Longrightarrow> let x = foo in f x" by simp

lemma hlp1: 
	assumes fin: "finite k"
	assumes el: "(IF v t e) \<in> k"
	assumes a1: "x \<in> \<Union>((\<lambda>vr. ifex_variable_set (restrict vr (select_lowest (\<Union>(ifex_variable_set ` k))) vl)) ` k)" (is "x \<in> ?a1s")
	shows "select_lowest (\<Union>(ifex_variable_set ` k)) < x"
proof(cases "k = {}")
	case True
	have False using a1 unfolding True by simp
	thus ?thesis ..
next
	case False
	let ?vs = "\<Union>(ifex_variable_set ` k)"
	have "is_lowest_element (select_lowest ?vs) ?vs" 
		apply(rule select_is_lowest) 
		using finite_ifex_variable_set fin apply blast 
		using el apply force
	done
	moreover have ne: "select_lowest ?vs \<notin> ?a1s" using not_element_restrict by fast
	moreover have "\<Union>((\<lambda>vr. ifex_variable_set (restrict vr (select_lowest (\<Union>(ifex_variable_set ` k))) vl)) ` k) \<subseteq> (\<Union>(ifex_variable_set ` k))" 
		using restrict_variables_subset by fast
	moreover have "x \<noteq> select_lowest ?vs" using a1 ne by fast
	ultimately show ?thesis
				using a1 
		unfolding is_lowest_element_def
		unfolding Ball_def
		by fastforce
qed

lemma order_dings_invar: "ordner i \<Longrightarrow> ordner t \<Longrightarrow> ordner e \<Longrightarrow> ordner (dings i t e)"
	apply(induction i t e rule: dings.induct)
	  apply simp_all[2]
	apply(subst dings.simps)
	apply(unfold Let_keeper)
	apply(subst ordner.simps)
	apply(rule Let2assm)+
	apply rule
	 apply(blast intro: hlp1[OF finite_three] dest: subsetD[OF ifex_variable_set_dings_ss])
	apply(meson restrict_ordner_invar)
done

theorem "
	(ia, ib) \<in> ifex_bf2_rel \<Longrightarrow>
	(ta, tb) \<in> ifex_bf2_rel \<Longrightarrow>
	(ea, eb) \<in> ifex_bf2_rel \<Longrightarrow>
	(bf_ite ia ta ea, dings ib tb eb) \<in> ifex_bf2_rel"
proof(induction ib tb eb arbitrary: ia ta ea rule: dings.induct)
	case goal3 note goal1 = goal3
	let ?strtr = "select_lowest (\<Union>(ifex_variable_set ` {IF iv it ie, t, e}))"
	have mrdr: "ordner (IF ?strtr (dings (restrict (IF iv it ie) ?strtr True) (restrict t ?strtr True) (restrict e ?strtr True))
                                  (dings (restrict (IF iv it ie) ?strtr False) (restrict t ?strtr False) (restrict e ?strtr False)))"
		unfolding ordner.simps
		by(rule conjI, rule, unfold Un_iff, erule disjE)
		    (((drule subsetD[OF ifex_variable_set_dings_ss], 
			unfold img_three, blast intro: hlp1[where k = "{IF iv it ie, t, e}", OF finite_three, unfolded img_three])+),
			metis restrict_ordner_invar order_dings_invar ordner_implied goal1(3,4,5))
    have kll: "(\<lambda>as. if as ?strtr then bf_ite (bf2_restrict ?strtr True ia) (bf2_restrict ?strtr True ta) (bf2_restrict ?strtr True ea) as
                                   else bf_ite (bf2_restrict ?strtr False ia) (bf2_restrict ?strtr False ta) (bf2_restrict ?strtr False ea) as) 
               = bf_ite ia ta ea"
               unfolding bf_ite_def bf2_restrict_def fun_eq_iff
               by(simp add: fun_upd_idem)+
	note (* free the induction hypotheses *)  
		goal1(1)[OF refl refl restrict_ifex_bf2_rel[OF goal1(3)] restrict_ifex_bf2_rel[OF goal1(4)] restrict_ifex_bf2_rel [OF goal1(5)]]
		goal1(2)[OF refl refl restrict_ifex_bf2_rel[OF goal1(3)] restrict_ifex_bf2_rel[OF goal1(4)] restrict_ifex_bf2_rel [OF goal1(5)]]
	note ifex_bf2_construct(* this is basically the central property *)[OF this mrdr] 
	thus ?case unfolding dings.simps Let_def kll by blast
qed (frule rel_true_false, simp only: dings.simps bf_ite_def const_def if_True if_False)+

fun restrict_top :: "('a :: linorder) ifex \<Rightarrow> bool \<Rightarrow> 'a ifex" where
  "restrict_top (IF v t e) val = (if val then t else e)" |
  "restrict_top i _ = i"
  
lemma restrict_untouched_id: "x \<notin> ifex_variable_set t \<Longrightarrow> restrict t x val = t" (* umkehrung gilt auch\<dots> *)
proof(induction t)
	case (IF v t e)
	from IF.prems have "x \<notin> ifex_variable_set t" "x \<notin> ifex_variable_set e" by auto
	note mIH = IF.IH(1)[OF this(1)] IF.IH(2)[OF this(2)]
	from IF.prems have "x \<noteq> v" by simp
	thus ?case unfolding restrict.simps Let_def mIH  by simp
qed simp_all

lemma "ordner (IF v t e) \<Longrightarrow> restrict (IF v t e) v val = restrict_top (IF v t e) val"
	using restrict_untouched_id by fastforce (* fastforce ftw *)


(* INDUCTIVE DEFINITION *)

abbreviation ifex_variables_ite where 
  "ifex_variables_ite i t e \<equiv> 
   ifex_variable_set i \<union> ifex_variable_set t \<union> ifex_variable_set e"

inductive ind_ite :: "('a::linorder) ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> bool" where
ind_ite_true:   "ind_ite t Trueif t e" |
ind_ite_false:  "ind_ite e Falseif t e" |
ind_ite_if:     "x \<in> ifex_variables_ite i t e \<Longrightarrow>
   \<forall>v \<in> ifex_variables_ite i t e. x \<le> v \<Longrightarrow>
   i = IF iv tifex eifex \<Longrightarrow>
   ind_ite l (restrict i x True) (restrict t x True) (restrict e x True) \<Longrightarrow>
   ind_ite r (restrict i x False) (restrict t x False) (restrict e x False) \<Longrightarrow>
   ind_ite (IF x l r) i t e"

lemma ifex_variable_set_union_image_equi:
  "\<Union>(ifex_variable_set ` {i,t,e}) =
   ifex_variable_set i \<union> ifex_variable_set t \<union> ifex_variable_set e"
  by blast

lemma pleasecombinemewith2: "ind_ite b i t e \<Longrightarrow> dings i t e = b"
proof(induction rule: ind_ite.induct)
  case(ind_ite_if x i t e iv tifex eifex l r)
    from this(3) have "ifex_variables_ite i t e \<noteq> {}" "finite (ifex_variables_ite i t e)"
      using finite_ifex_variable_set by auto
    from  select_is_lowest[OF this(2) this(1)] ind_ite_if(1,2)
      have "select_lowest (\<Union>(ifex_variable_set ` {i, t, e})) = x"
      unfolding is_lowest_element_def by (subst ifex_variable_set_union_image_equi) force
    from this ind_ite_if(3)
      have "select_lowest (\<Union>(ifex_variable_set ` {IF iv tifex eifex, t, e})) = x" by simp
    from this ind_ite_if(3,6,7) show ?case by simp
qed (auto)

lemma pleasecombinemewith1: "dings i t e = b \<Longrightarrow> ind_ite b i t e"
proof(induct arbitrary: b rule: dings.induct)
  case("3" iv tifex eifex t e) note dings_IF = "3"
  obtain i where i_def: "i = IF iv tifex eifex" by simp
  then obtain y where y_def: "y = select_lowest (\<Union>(ifex_variable_set ` {i,t,e}))" by simp
  from i_def have "finite (ifex_variables_ite i t e)" "ifex_variables_ite i t e \<noteq> {}"
    by (simp_all add: finite_ifex_variable_set)
  from select_is_lowest[OF this(1) this(2)] y_def
    have smallest: "y \<in> ifex_variables_ite i t e" "\<forall>v \<in> ifex_variables_ite i t e. y \<le> v"
    unfolding is_lowest_element_def by (simp_all only: ifex_variable_set_union_image_equi) (simp)
  obtain l where l_def: "l = dings (restrict i y True) (restrict t y True) (restrict e y True)"
    by simp
  with i_def y_def dings_IF(1)[of i y l] 
    have left: "ind_ite l (restrict i y True) (restrict t y True) (restrict e y True)" by simp
  obtain r where r_def: "r = dings (restrict i y False) (restrict t y False) (restrict e y False)" 
    by simp
  with i_def y_def dings_IF(2)[of i y r] 
    have right: "ind_ite r (restrict i y False) (restrict t y False) (restrict e y False)" by simp
  from dings_IF(3) l_def r_def y_def i_def have "b = IF y l r" by simp
  with ind_ite_if[OF smallest i_def left right] show ?case using i_def by simp
qed (auto simp add: ind_ite.intros)

lemma "dings i t e = b \<longleftrightarrow> ind_ite b i t e"
  using pleasecombinemewith1 pleasecombinemewith2 by blast

lemma "ind_ite Falseif Trueif Falseif Trueif" apply(rule ind_ite_true) done

lemma "ind_ite (IF 1 (IF 2 Falseif Trueif) Trueif) 
              (IF (1::nat) (IF 2 Trueif Falseif) Falseif) (Falseif) (Trueif)"
  apply(rule) apply(force) apply(auto) apply(rule) apply(auto) using ind_ite.intros apply(auto) done

value "dings (IF (1::nat) (IF 2 Trueif Falseif) Falseif) (Falseif) (Trueif)"

(* The following proofs could probably be very easily automated *)

lemma ind_ite_variables_subset: "ind_ite b i t e \<Longrightarrow> 
  ifex_variable_set b \<subseteq> ifex_variable_set i \<union> ifex_variable_set t \<union> ifex_variable_set e"
proof(induction rule: ind_ite.induct)
  case(ind_ite_if x i t e iv tv ev l r) 
    from this(6,7) have 
         "ifex_variable_set l \<subseteq> ifex_variables_ite i t e"
         "ifex_variable_set r \<subseteq> ifex_variables_ite i t e"
        using restrict_variables_subset[of i x True] restrict_variables_subset[of t x True] 
              restrict_variables_subset[of e x True] restrict_variables_subset[of i x False]
              restrict_variables_subset[of t x False] restrict_variables_subset[of e x False]
        by (auto)
     with ind_ite_if(1) show ?case by simp
qed (auto)

lemma ind_ite_not_element: "ind_ite b i t e \<Longrightarrow> x \<notin> ifex_variables_ite i t e  \<Longrightarrow>
                            x \<notin> ifex_variable_set b"
proof(induction arbitrary: x rule: ind_ite.induct)
  case(ind_ite_if y i t e iv tv ev l r) 
    from this(1,8) this(6)[of x] this(7)[of x]
    have "x \<noteq> y" "x \<notin> ifex_variable_set l" "x \<notin> ifex_variable_set r"
      using restrict_variables_subset contra_subsetD by (fastforce)+
    thus ?case by simp
qed (auto)

lemma ind_ite_ordner: "ind_ite b i t e \<Longrightarrow> ordner i \<Longrightarrow> ordner t \<Longrightarrow> ordner e \<Longrightarrow> ordner b"
proof(induction rule: ind_ite.induct)
  case(ind_ite_if x i t e iv tv ev l r) from this(6,7,8,9,10) have 0: "ordner l" "ordner r" 
    using restrict_ordner_invar by auto
  from ind_ite_if(4,5) have 1:"x \<notin> ifex_variable_set l" "x \<notin> ifex_variable_set r" 
     using ind_ite_not_element not_element_restrict by fastforce+
  from ind_ite_if(2) ind_ite_variables_subset[OF ind_ite_if(4)]
    have 2: "\<forall>y \<in> ifex_variable_set l. x \<le> y" using restrict_variables_subset by fast
  from ind_ite_if(2) ind_ite_variables_subset[OF ind_ite_if(5)]
    have 3: "\<forall>y \<in> ifex_variable_set r. x \<le> y" using restrict_variables_subset by fast
  from 0 1 2 3 show ?case using le_neq_trans by fastforce
qed (simp)

lemma helperino: "ass y = x \<Longrightarrow> bf_ite ia ta ea ass = bf_ite (bf2_restrict y x ia) (bf2_restrict y x ta) 
                     (bf2_restrict y x ea) ass"
  unfolding bf_ite_def bf2_restrict_def by force
lemma ind_ite_val_invar: "ind_ite b ib tb eb \<Longrightarrow>
       \<forall>ass. ia ass = val_ifex ib ass \<Longrightarrow>
       \<forall>ass. ta ass = val_ifex tb ass \<Longrightarrow>
       \<forall>ass. ea ass = val_ifex eb ass \<Longrightarrow>
       \<forall>ass. (bf_ite ia ta ea) ass = val_ifex b ass"
proof(induction arbitrary: ia ta ea rule: ind_ite.induct)
  case(ind_ite_if y i t e iv tv ev l r)
  note ffs1 = restrict_val_invar[OF ind_ite_if(8)] and (* ffs = for fucks sake *)
       ffs2 = restrict_val_invar[OF ind_ite_if(9)] and
       ffs3 = restrict_val_invar[OF ind_ite_if(10)]
  from ind_ite_if(6)[of "bf2_restrict y True ia" "bf2_restrict y True ta" "bf2_restrict y True ea"]
       ffs1[of y True] ffs2 [of y True] ffs3[of y True]
  have 0: "\<forall>ass. bf_ite (bf2_restrict y True ia) (bf2_restrict y True ta) 
                     (bf2_restrict y True ea) ass 
              = val_ifex l ass" by fastforce
  note ffs1 = restrict_val_invar[OF ind_ite_if(8)] and (* ffs = for fucks sake *)
       ffs2 = restrict_val_invar[OF ind_ite_if(9)] and
       ffs3 = restrict_val_invar[OF ind_ite_if(10)]
  from ind_ite_if(7)[of "bf2_restrict y False ia" 
                        "bf2_restrict y False ta" "bf2_restrict y False ea"]
       ffs1[of y False] ffs2 [of y False] ffs3[of y False]
  have 1: "\<forall>ass. bf_ite (bf2_restrict y False ia) (bf2_restrict y False ta) 
                     (bf2_restrict y False ea) ass 
              = val_ifex r ass" by fastforce
  have "\<And>ass. ass y \<Longrightarrow> bf_ite ia ta ea ass = bf_ite (bf2_restrict y True ia) (bf2_restrict y True ta) 
                     (bf2_restrict y True ea) ass"
                    "\<And>ass. \<not> ass y \<Longrightarrow> bf_ite ia ta ea ass = bf_ite (bf2_restrict y False ia) (bf2_restrict y False ta) 
                     (bf2_restrict y False ea) ass" using helperino[of _ y True ia ta ea]
                                                          helperino[of _ y False ia ta ea] by force+
  from 0 1 this show ?case by simp
qed (auto simp add: bf_ite_def)

lemma "ind_ite b ib tb eb \<Longrightarrow>
       (ia, ib) \<in> ifex_bf2_rel \<Longrightarrow>
	     (ta, tb) \<in> ifex_bf2_rel \<Longrightarrow>
	     (ea, eb) \<in> ifex_bf2_rel \<Longrightarrow>
	     (bf_ite ia ta ea, b) \<in> ifex_bf2_rel"
  unfolding ifex_bf2_rel_def by (simp add: ind_ite_ordner ind_ite_val_invar)

end

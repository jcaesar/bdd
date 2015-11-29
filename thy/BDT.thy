theory BDT
imports Boolean_Expression_Checkers BoolFunc Min2
begin

(* datatype 'a ifex = Trueif | Falseif | IF 'a "'a ifex" "'a ifex" *)
(* type_synonym boolfunc2 = "(nat \<Rightarrow> bool) \<Rightarrow> bool" *)


fun ifex_var_set :: "'a ifex \<Rightarrow> 'a set" where
  "ifex_var_set (IF v t e) = {v} \<union> ifex_var_set t \<union> ifex_var_set e" |
  "ifex_var_set Trueif = {}" |
  "ifex_var_set Falseif = {}"

fun ifex_ordered :: "('a::linorder) ifex \<Rightarrow> bool" where
  "ifex_ordered (IF v t e) = ((\<forall>tv \<in> (ifex_var_set t \<union> ifex_var_set e). v < tv)
                       \<and> ifex_ordered t \<and> ifex_ordered e)" |
  "ifex_ordered Trueif = True" |
  "ifex_ordered Falseif = True"

definition ifex_bf2_rel where
  "ifex_bf2_rel = {(a,b). (\<forall>ass. a ass \<longleftrightarrow> val_ifex b ass) \<and> ifex_ordered b}"

lemma finite_ifex_var_set: "finite (ifex_var_set k)" by(induction k) simp_all
lemma nonempty_if_var_set: "ifex_var_set (IF v t e) \<noteq> {}" by simp
lemma ifex_ite_select_helper: "i = (IF iv it ie) \<Longrightarrow> k = (\<Union>(ifex_var_set ` {i,t,e})) \<Longrightarrow> finite k \<and> k \<noteq> {}"
	using finite_ifex_var_set nonempty_if_var_set by auto

fun restrict where
  "restrict (IF v t e) var val = (let rt = restrict t var val; re = restrict e var val in
                   (if v = var then (if val then rt else re) else (IF v rt re)))" |
  "restrict i _ _ = i"

value "ifex_ordered (IF 1 Falseif (IF (0::nat) (IF 0 Falseif Falseif) Falseif))"
value "restrict (IF (1::nat) Falseif (IF 0 (IF 0 Falseif Falseif) Falseif)) 1 False"
(* definition "bf2_restrict (i::nat) (val::bool) (func::boolfunc2) \<equiv> (\<lambda>v. func (v(i:=val)))" *)
value "ifex_ordered (IF (0::nat) (IF 0 Falseif Falseif) Falseif)"

declare Let_def[simp]

lemma not_element_restrict: "var \<notin> ifex_var_set (restrict b var val)"
  by (induction b) auto

lemma restrict_assignment: "val_ifex b (ass(var := val)) \<longleftrightarrow> val_ifex (restrict b var val) ass"
  by (induction b) auto

lemma restrict_variables_subset: "ifex_var_set (restrict b var val) \<subseteq> ifex_var_set b"
  by (induction b) auto

lemma restrict_ifex_ordered_invar: "ifex_ordered b \<Longrightarrow> ifex_ordered (restrict b var val)"
  using restrict_variables_subset by (induction b) (fastforce)+

lemma restrict_val_invar: "\<forall>ass. a ass = val_ifex b ass \<Longrightarrow> 
      (bf2_restrict var val a) ass = val_ifex (restrict b var val) ass"
  unfolding bf2_restrict_def using restrict_assignment by simp

lemma restrict_ifex_bf2_rel:
"(a, b) \<in> ifex_bf2_rel \<Longrightarrow> (bf2_restrict var val a, restrict b var val) \<in> ifex_bf2_rel"
  unfolding ifex_bf2_rel_def using restrict_ifex_ordered_invar restrict_val_invar
  by (clarsimp simp add: bf2_restrict_def restrict_assignment)

function ifex_ite :: "'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> ('a :: linorder) ifex" where
  "ifex_ite Trueif t e = t" |
  "ifex_ite Falseif t e = e" |
  "ifex_ite (IF iv it ie) t e = (let i = (IF iv it ie); x = select_lowest (\<Union>(ifex_var_set ` {i,t,e})) in 
                         (IF x (ifex_ite (restrict i x True) (restrict t x True) (restrict e x True))
                               (ifex_ite (restrict i x False) (restrict t x False) (restrict e x False))))"
by pat_completeness auto

lemma restrict_size_le: "size (restrict k x val) \<le> size k"
by(induction k) (auto)
lemma restrict_size_less: "x \<in> ifex_var_set k \<Longrightarrow> size (restrict k x val) < size k"
proof(induction k)
	case (IF v t e)
	thus ?case
	proof(cases "v = x")
		case True
		show ?thesis by(simp only: True restrict.simps refl if_True) (cases val, simp_all add: preorder_class.le_less_trans[OF restrict_size_le])
	next
		case False note of = this
		show ?thesis
		proof(cases "x \<in> ifex_var_set t")
			case True
			show ?thesis by(simp only: restrict.simps False if_False ifex.size) (simp add: IF.IH(1)[OF True] restrict_size_le add.commute add_le_less_mono)
		next
			case False
			have *: "x \<in> ifex_var_set e"
			proof(rule ccontr)
				assume "x \<notin> ifex_var_set e"
				note this False `v \<noteq> x`
				with IF.prems show False by simp
			qed
			show ?thesis by(simp only: restrict.simps of if_False ifex.size) (simp add: IF.IH(2)[OF *] add_mono_thms_linordered_field(4) restrict_size_le)
		qed
	qed
qed simp_all
lemma restrict_size_eqE: "size k = size (restrict k x val) \<Longrightarrow> x \<notin> ifex_var_set k"
	using less_not_refl restrict_size_less by metis

lemma termlemma2: "xa = select_lowest (\<Union>(ifex_var_set ` {(IF iv it ie), t, e})) \<Longrightarrow>
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
		then show False unfolding goal1 using ifex_ite_select_helper[OF refl refl] 
			conjunct1[OF select_is_lowest[unfolded is_lowest_element_def], of "(\<Union>(ifex_var_set ` {(IF iv it ie), t, e}))"] by auto 
	next
		case True thus False using restrict_size_le by (metis add_mono_thms_linordered_semiring(1) leD)
	qed
qed
lemma termlemma: "xa = select_lowest (\<Union>(ifex_var_set ` {(IF iv it ie), t, e})) \<Longrightarrow>
       (case (restrict (IF iv it ie) xa val, restrict t xa val, restrict e xa val) of (i, t, e) \<Rightarrow> size i + size t + size e) < (case (IF iv it ie, t, e) of (i, t, e) \<Rightarrow> size i + size t + size e)"
using termlemma2 by fast
termination ifex_ite by(relation "measure (\<lambda>(i,t,e). size i + size t + size e)", rule wf_measure, unfold in_measure) (simp_all only: termlemma)+

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
unfolding ifex_ordered.simps
unfolding bf2_restrict_def
oops
lemma ifex_bf2_construct: "(ta, tb) \<in> ifex_bf2_rel \<Longrightarrow> (ea, eb) \<in> ifex_bf2_rel \<Longrightarrow> ifex_ordered (IF x tb eb) \<Longrightarrow> (\<lambda>as. if as x then ta as else ea as, IF x tb eb) \<in> ifex_bf2_rel"
	unfolding fun_eq_iff const_def
	unfolding ifex_bf2_rel_def
	by simp
	
lemma ifex_ordered_implied: "(a, b) \<in> ifex_bf2_rel \<Longrightarrow> ifex_ordered b" unfolding ifex_bf2_rel_def by simp

lemma img_three: "foo ` {a, b, c} = {foo a, foo b, foo c}" by simp
lemma Un_three: "\<Union>{a, b, c} = a \<union> b \<union> c" by auto
lemma finite_three: "finite {a, b, c}" by simp

lemma single_valued_rel: "single_valued (ifex_bf2_rel\<inverse>)"
	unfolding single_valued_def
	unfolding ifex_bf2_rel_def
	unfolding converse_unfold
	unfolding in_rel_def[symmetric]  in_rel_Collect_split_eq
	by blast

lemma ifex_var_set_ifex_ite_ss: "ifex_var_set (ifex_ite i t e) \<subseteq> \<Union>(ifex_var_set ` {i, t, e})"
	apply(induction i t e rule: ifex_ite.induct)
	  apply simp_all[2]
	apply(subst ifex_ite.simps)
	apply(unfold Let_def)
	apply(subst ifex_var_set.simps)
	apply(rule le_supI)
	 apply(rule le_supI)
	  apply rule
	  apply(unfold singleton_iff)
	  apply(meson ifex_ite_select_helper is_lowest_element_def select_is_lowest)
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
	assumes a1: "x \<in> \<Union>((\<lambda>vr. ifex_var_set (restrict vr (select_lowest (\<Union>(ifex_var_set ` k))) vl)) ` k)" (is "x \<in> ?a1s")
	shows "select_lowest (\<Union>(ifex_var_set ` k)) < x"
proof(cases "k = {}")
	case True
	have False using a1 unfolding True by simp
	thus ?thesis ..
next
	case False
	let ?vs = "\<Union>(ifex_var_set ` k)"
	have "is_lowest_element (select_lowest ?vs) ?vs" 
		using finite_ifex_var_set fin el 
		by(force intro: select_is_lowest)
	moreover have ne: "select_lowest ?vs \<notin> ?a1s" using not_element_restrict by fast
	moreover have "\<Union>((\<lambda>vr. ifex_var_set (restrict vr (select_lowest (\<Union>(ifex_var_set ` k))) vl)) ` k) \<subseteq> (\<Union>(ifex_var_set ` k))" 
		using restrict_variables_subset by fast
	moreover have "x \<noteq> select_lowest ?vs" using a1 ne by fast
	ultimately show ?thesis
				using a1 
		unfolding is_lowest_element_def
		unfolding Ball_def
		by(auto dest: le_neq_trans)
qed

lemma order_ifex_ite_invar: "ifex_ordered i \<Longrightarrow> ifex_ordered t \<Longrightarrow> ifex_ordered e \<Longrightarrow> ifex_ordered (ifex_ite i t e)"
	apply(induction i t e rule: ifex_ite.induct)
	  apply simp_all[2]
	apply(subst ifex_ite.simps)
	apply(unfold Let_keeper)
	apply(subst ifex_ordered.simps)
	apply(rule Let2assm)+
	apply rule
	 apply(blast intro: hlp1[OF finite_three] dest: subsetD[OF ifex_var_set_ifex_ite_ss])
	apply(meson restrict_ifex_ordered_invar)
done

theorem "
	(ia, ib) \<in> ifex_bf2_rel \<Longrightarrow>
	(ta, tb) \<in> ifex_bf2_rel \<Longrightarrow>
	(ea, eb) \<in> ifex_bf2_rel \<Longrightarrow>
	(bf_ite ia ta ea, ifex_ite ib tb eb) \<in> ifex_bf2_rel"
proof(induction ib tb eb arbitrary: ia ta ea rule: ifex_ite.induct)
	case goal3 note goal1 = goal3
	let ?strtr = "select_lowest (\<Union>(ifex_var_set ` {IF iv it ie, t, e}))"
	have mrdr: "ifex_ordered (IF ?strtr (ifex_ite (restrict (IF iv it ie) ?strtr True) (restrict t ?strtr True) (restrict e ?strtr True))
                                  (ifex_ite (restrict (IF iv it ie) ?strtr False) (restrict t ?strtr False) (restrict e ?strtr False)))"
		unfolding ifex_ordered.simps
		by(rule conjI, rule, unfold Un_iff, erule disjE)
		    (((drule subsetD[OF ifex_var_set_ifex_ite_ss], 
			unfold img_three, blast intro: hlp1[where k = "{IF iv it ie, t, e}", OF finite_three, unfolded img_three])+),
			metis restrict_ifex_ordered_invar order_ifex_ite_invar ifex_ordered_implied goal1(3,4,5))
    have kll: "(\<lambda>as. if as ?strtr then bf_ite (bf2_restrict ?strtr True ia) (bf2_restrict ?strtr True ta) (bf2_restrict ?strtr True ea) as
                                   else bf_ite (bf2_restrict ?strtr False ia) (bf2_restrict ?strtr False ta) (bf2_restrict ?strtr False ea) as) 
               = bf_ite ia ta ea"
               unfolding bf_ite_def bf2_restrict_def fun_eq_iff
               by(simp add: fun_upd_idem)+
	note (* free the induction hypotheses *)  
		goal1(1)[OF refl refl restrict_ifex_bf2_rel[OF goal1(3)] restrict_ifex_bf2_rel[OF goal1(4)] restrict_ifex_bf2_rel [OF goal1(5)]]
		goal1(2)[OF refl refl restrict_ifex_bf2_rel[OF goal1(3)] restrict_ifex_bf2_rel[OF goal1(4)] restrict_ifex_bf2_rel [OF goal1(5)]]
	note ifex_bf2_construct(* this is basically the central property *)[OF this mrdr] 
	thus ?case unfolding ifex_ite.simps Let_def kll by blast
qed (frule rel_true_false, simp only: ifex_ite.simps bf_ite_def const_def if_True if_False)+

fun restrict_top :: "('a :: linorder) ifex \<Rightarrow> bool \<Rightarrow> 'a ifex" where
  "restrict_top (IF v t e) val = (if val then t else e)" |
  "restrict_top i _ = i"
  
lemma restrict_untouched_id: "x \<notin> ifex_var_set t \<Longrightarrow> restrict t x val = t" (* umkehrung gilt auch\<dots> *)
proof(induction t)
	case (IF v t e)
	from IF.prems have "x \<notin> ifex_var_set t" "x \<notin> ifex_var_set e" by auto
	note mIH = IF.IH(1)[OF this(1)] IF.IH(2)[OF this(2)]
	from IF.prems have "x \<noteq> v" by simp
	thus ?case unfolding restrict.simps Let_def mIH  by simp
qed simp_all

lemma "ifex_ordered (IF v t e) \<Longrightarrow> restrict (IF v t e) v val = restrict_top (IF v t e) val"
	using restrict_untouched_id by fastforce (* fastforce ftw *)


(* INDUCTIVE DEFINITION *)

abbreviation ifex_variables_ite where 
  "ifex_variables_ite i t e \<equiv> 
   ifex_var_set i \<union> ifex_var_set t \<union> ifex_var_set e"

inductive ind_ite :: "('a::linorder) ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> bool" where
ind_ite_true:   "ind_ite t Trueif t e" |
ind_ite_false:  "ind_ite e Falseif t e" |
ind_ite_if:     "x \<in> ifex_variables_ite i t e \<Longrightarrow>
   \<forall>v \<in> ifex_variables_ite i t e. x \<le> v \<Longrightarrow>
   i = IF iv tifex eifex \<Longrightarrow>
   ind_ite l (restrict i x True) (restrict t x True) (restrict e x True) \<Longrightarrow>
   ind_ite r (restrict i x False) (restrict t x False) (restrict e x False) \<Longrightarrow>
   ind_ite (IF x l r) i t e"

lemma ifex_var_set_union_image_equi:
  "\<Union>(ifex_var_set ` {i,t,e}) =
   ifex_var_set i \<union> ifex_var_set t \<union> ifex_var_set e"
  by blast

lemma "ifex_ite i t e = b \<longleftrightarrow> ind_ite b i t e"
proof(rule iffI)
assume "ifex_ite i t e = b" thus "ind_ite b i t e"
proof(induct arbitrary: b rule: ifex_ite.induct)
  case("3" iv tifex eifex t e) note ifex_ite_IF = "3"
  obtain i y l r 
    where i_def: "i = IF iv tifex eifex" and
          y_def: "y = select_lowest (\<Union>(ifex_var_set ` {i,t,e}))" and
          r_def: "r = ifex_ite (restrict i y False) (restrict t y False) (restrict e y False)" and
          l_def: "l = ifex_ite (restrict i y True) (restrict t y True) (restrict e y True)" by simp
  from i_def have "finite (ifex_variables_ite i t e)" "ifex_variables_ite i t e \<noteq> {}"
    by (simp_all add: finite_ifex_var_set)
  from select_is_lowest[OF this(1) this(2)] y_def
    have smallest: "y \<in> ifex_variables_ite i t e" "\<forall>v \<in> ifex_variables_ite i t e. y \<le> v"
    unfolding is_lowest_element_def by (simp_all only: ifex_var_set_union_image_equi) (simp)
  from l_def r_def i_def y_def ifex_ite_IF(1)[of i y l] ifex_ite_IF(2)[of i y r] 
    have landr: "ind_ite l (restrict i y True) (restrict t y True) (restrict e y True)"
                "ind_ite r (restrict i y False) (restrict t y False) (restrict e y False)" by auto
  from ifex_ite_IF(3) l_def r_def y_def i_def have "b = IF y l r" by simp
  with ind_ite_if[OF smallest i_def landr] show ?case using i_def by simp
qed (auto simp add: ind_ite.intros)
next
assume "ind_ite b i t e" thus "ifex_ite i t e = b"
proof(induction rule: ind_ite.induct)
  case(ind_ite_if x i t e iv tifex eifex l r)
    from this(3) have "ifex_variables_ite i t e \<noteq> {}" "finite (ifex_variables_ite i t e)"
      using finite_ifex_var_set by auto
    from select_is_lowest[OF this(2) this(1)] ind_ite_if(1,2,3)
      have "select_lowest (\<Union>(ifex_var_set ` {IF iv tifex eifex, t, e})) = x"
      unfolding is_lowest_element_def by (subst ifex_var_set_union_image_equi) force
    from this ind_ite_if(3,6,7) show ?case by simp
qed (auto)
qed

lemma ind_ite_variables_subset: "ind_ite b i t e \<Longrightarrow> 
  ifex_var_set b \<subseteq> ifex_var_set i \<union> ifex_var_set t \<union> ifex_var_set e"
proof(induction rule: ind_ite.induct)
  case(ind_ite_if x i t e iv tv ev l r) 
    from this(6,7) restrict_variables_subset[of _ x _] have 
         "ifex_var_set l \<subseteq> ifex_variables_ite i t e"
         "ifex_var_set r \<subseteq> ifex_variables_ite i t e"
        by (blast)+
     with ind_ite_if(1) show ?case by simp
qed (auto)

lemma ind_ite_not_element: "ind_ite b i t e \<Longrightarrow> x \<notin> ifex_variables_ite i t e  \<Longrightarrow>
                            x \<notin> ifex_var_set b"
proof(induction arbitrary: x rule: ind_ite.induct)
  case(ind_ite_if y i t e iv tv ev l r) 
    from this(1,8) this(6)[of x] this(7)[of x]
    have "x \<noteq> y" "x \<notin> ifex_var_set l" "x \<notin> ifex_var_set r"
      using restrict_variables_subset contra_subsetD by (fastforce)+
    thus ?case by simp
qed (auto)

lemma ind_ite_ifex_ordered: "ind_ite b i t e \<Longrightarrow> 
                             ifex_ordered i \<Longrightarrow> ifex_ordered t \<Longrightarrow> ifex_ordered e \<Longrightarrow> 
                             ifex_ordered b"
proof(induction rule: ind_ite.induct)
  case(ind_ite_if x i t e iv tv ev l r) from this(6,7,8,9,10) 
    have 0: "ifex_ordered l" "ifex_ordered r" 
    using restrict_ifex_ordered_invar by auto
  from ind_ite_if(4,5) have 1:"x \<notin> ifex_var_set l" "x \<notin> ifex_var_set r" 
     using ind_ite_not_element not_element_restrict by fastforce+
  from ind_ite_if(2) ind_ite_variables_subset[OF ind_ite_if(4)]
    have 2: "\<forall>y \<in> ifex_var_set l. x \<le> y" using restrict_variables_subset by fast
  from ind_ite_if(2) ind_ite_variables_subset[OF ind_ite_if(5)]
    have 3: "\<forall>y \<in> ifex_var_set r. x \<le> y" using restrict_variables_subset by fast
  from 0 1 2 3 show ?case using le_neq_trans by fastforce
qed (simp)

lemma bf_ite_assignment_invar:
  "ass y = x \<Longrightarrow> bf_ite ia ta ea ass = bf_ite (bf2_restrict y x ia) (bf2_restrict y x ta) 
                                              (bf2_restrict y x ea) ass"
  unfolding bf_ite_def bf2_restrict_def by force

lemma ind_ite_val_invar: "ind_ite b ib tb eb \<Longrightarrow>
  \<forall>ass. ia ass = val_ifex ib ass \<Longrightarrow>
  \<forall>ass. ta ass = val_ifex tb ass \<Longrightarrow>
  \<forall>ass. ea ass = val_ifex eb ass \<Longrightarrow>
  \<forall>ass. (bf_ite ia ta ea) ass = val_ifex b ass"
proof(induction arbitrary: ia ta ea rule: ind_ite.induct)
  case(ind_ite_if y i t e iv tv ev l r)
  note rvi_mult = restrict_val_invar[OF ind_ite_if(8)]
                  restrict_val_invar[OF ind_ite_if(9)]
                  restrict_val_invar[OF ind_ite_if(10)]
  from ind_ite_if(6) ind_ite_if(7) rvi_mult bf_ite_assignment_invar[of _ y _ ia ta ea]
    have "\<forall>ass. bf_ite (bf2_restrict y True ia) (bf2_restrict y True ta)
                       (bf2_restrict y True ea) ass
                 = val_ifex l ass" 
         "\<forall>ass. bf_ite (bf2_restrict y False ia) (bf2_restrict y False ta)
                       (bf2_restrict y False ea) ass
                = val_ifex r ass"
         "\<And>ass. ass y \<Longrightarrow> bf_ite ia ta ea ass =
                           bf_ite (bf2_restrict y True ia) (bf2_restrict y True ta)
                                  (bf2_restrict y True ea) ass"
         "\<And>ass. \<not> ass y \<Longrightarrow> bf_ite ia ta ea ass =
                             bf_ite (bf2_restrict y False ia) (bf2_restrict y False ta) 
                                    (bf2_restrict y False ea) ass"
       by fastforce+
  thus ?case by simp
qed (auto simp add: bf_ite_def)

lemma "ind_ite b ib tb eb \<Longrightarrow>
       (ia, ib) \<in> ifex_bf2_rel \<Longrightarrow>
       (ta, tb) \<in> ifex_bf2_rel \<Longrightarrow>
       (ea, eb) \<in> ifex_bf2_rel \<Longrightarrow>
       (bf_ite ia ta ea, b) \<in> ifex_bf2_rel"
  unfolding ifex_bf2_rel_def by (simp add: ind_ite_ifex_ordered ind_ite_val_invar)

end

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
  "ifex_ite (IF iv it ie) t e = (let i = (IF iv it ie); x = select_lowest (\<Union>(ifex_var_set ` {i,t,e}));
                                 l = ifex_ite (restrict i x True) (restrict t x True) (restrict e x True);
                                 r = ifex_ite (restrict i x False) (restrict t x False) (restrict e x False) in 
                        if l = r then l else IF x l r)"
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

lemma restrict_untouched_id: "x \<notin> ifex_var_set t \<Longrightarrow> restrict t x val = t" (* umkehrung gilt auch\<dots> *)
proof(induction t)
	case (IF v t e)
	from IF.prems have "x \<notin> ifex_var_set t" "x \<notin> ifex_var_set e" by auto
	note mIH = IF.IH(1)[OF this(1)] IF.IH(2)[OF this(2)]
	from IF.prems have "x \<noteq> v" by simp
	thus ?case unfolding restrict.simps Let_def mIH  by simp
qed simp_all

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
   ind_ite (if l = r then l else IF x l r) i t e"

lemma ifex_var_set_union_image_equi:
  "\<Union>(ifex_var_set ` {i,t,e}) =
   ifex_var_set i \<union> ifex_var_set t \<union> ifex_var_set e"
  by blast

lemma ifex_ite_ind_ite_equi: "ifex_ite i t e = b \<longleftrightarrow> ind_ite b i t e"
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
  from l_def r_def i_def y_def ifex_ite_IF(1)[of i y l] ifex_ite_IF(2)[of i y l r] 
    have landr: "ind_ite l (restrict i y True) (restrict t y True) (restrict e y True)"
                "ind_ite r (restrict i y False) (restrict t y False) (restrict e y False)" by auto
  from ifex_ite_IF(3) l_def r_def y_def i_def have "b = (if l = r then l else IF y l r)" by force
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
  thus ?case by force
qed (auto simp add: bf_ite_def)

lemma "ind_ite b ib tb eb \<Longrightarrow>
       (ia, ib) \<in> ifex_bf2_rel \<Longrightarrow>
       (ta, tb) \<in> ifex_bf2_rel \<Longrightarrow>
       (ea, eb) \<in> ifex_bf2_rel \<Longrightarrow>
       (bf_ite ia ta ea, b) \<in> ifex_bf2_rel"
  unfolding ifex_bf2_rel_def by (simp add: ind_ite_ifex_ordered ind_ite_val_invar)

fun ifex_minimal :: "'a ifex \<Rightarrow> bool" where
  "ifex_minimal (IF v t e) = ((t \<noteq> e) & ifex_minimal t & ifex_minimal e)" |
  "ifex_minimal Trueif = True" |
  "ifex_minimal Falseif = True"

lemma ifex_ordered_restrict_branches:
  "ifex_ordered (IF x l r) \<Longrightarrow> restrict (IF x l r) x val = (if val then l else r)"
  using restrict_untouched_id by fastforce

lemma ifex_minimal_restrict_invar:
       "ifex_ordered i \<Longrightarrow> ifex_minimal i \<Longrightarrow> \<forall>v \<in> ifex_var_set i. var \<le> v \<Longrightarrow>
       ifex_minimal (restrict i var val)"
proof(induction i)
case (IF x i1 i2) show ?case
proof(cases "var \<in> ifex_var_set (IF x i1 i2)")
  case False 
    with restrict_untouched_id have "(restrict (IF x i1 i2) var val) = (IF x i1 i2)" by fast
    with IF(4) show ?thesis by simp
  next
  case True
    with IF(3,5) have "var = x" apply(auto) using not_less by auto
    with IF(3,4) show ?thesis using ifex_ordered_restrict_branches by fastforce
  qed
qed (auto)

lemma ind_ite_minimal:
  "ind_ite b ib tb eb \<Longrightarrow> ifex_ordered ib \<Longrightarrow> ifex_ordered tb \<Longrightarrow> ifex_ordered eb \<Longrightarrow>
   ifex_minimal ib \<Longrightarrow> ifex_minimal tb \<Longrightarrow> ifex_minimal eb \<Longrightarrow>
   ifex_minimal b"
proof(induction rule: ind_ite.induct)
  case(ind_ite_if x i t e iv tifex eifex l r) 
    then have lr_minimal: "ifex_minimal l" "ifex_minimal r"
      using restrict_ifex_ordered_invar ifex_minimal_restrict_invar by(blast)+
    thus ?case by simp
qed (simp)


end

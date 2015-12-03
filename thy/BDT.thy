theory BDT
imports Boolean_Expression_Checkers BoolFunc Min2
begin

(* datatype 'a ifex = Trueif | Falseif | IF 'a "'a ifex" "'a ifex" *)
(* type_synonym boolfunc2 = "(nat \<Rightarrow> bool) \<Rightarrow> bool" *)


fun ifex_var_set :: "'a ifex \<Rightarrow> 'a set" where
  "ifex_var_set (IF v t e) = {v} \<union> ifex_var_set t \<union> ifex_var_set e" |
  "ifex_var_set Trueif = {}" |
  "ifex_var_set Falseif = {}"

fun ifex_top_var_set :: "'a ifex \<Rightarrow> 'a set" where
  "ifex_top_var_set (IF v t e) = {v}" |
  "ifex_top_var_set Trueif = {}" |
  "ifex_top_var_set Falseif = {}"

fun ifex_ordered :: "('a::linorder) ifex \<Rightarrow> bool" where
  "ifex_ordered (IF v t e) = ((\<forall>tv \<in> (ifex_var_set t \<union> ifex_var_set e). v < tv)
                       \<and> ifex_ordered t \<and> ifex_ordered e)" |
  "ifex_ordered Trueif = True" |
  "ifex_ordered Falseif = True"

fun ifex_minimal :: "('a::linorder) ifex \<Rightarrow> bool" where
  "ifex_minimal (IF v t e) = (t \<noteq> e \<and> ifex_minimal t \<and> ifex_minimal e)" |
  "ifex_minimal Trueif = True" |
  "ifex_minimal Falseif = True"

definition ifex_bf2_rel where
  "ifex_bf2_rel = {(a,b). (\<forall>ass. a ass \<longleftrightarrow> val_ifex b ass) \<and> ifex_ordered b \<and> ifex_minimal b}"

fun restrict where
  "restrict (IF v t e) var val = (let rt = restrict t var val; re = restrict e var val in
                   (if v = var then (if val then rt else re) else (IF v rt re)))" |
  "restrict i _ _ = i"

fun restrict_top where
  "restrict_top (IF v t e) var val =  (if v = var then (if val then t else e) else (IF v t e))" |
  "restrict_top Trueif var val = Trueif" |
  "restrict_top Falseif var val = Falseif"

function ifex_ite :: "'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> ('a :: linorder) ifex" where
  "ifex_ite Trueif t e = t" |
  "ifex_ite Falseif t e = e" |
  "ifex_ite (IF iv it ie) t e =
    (let i = (IF iv it ie); x = Min (\<Union>(ifex_top_var_set ` {i,t,e}));
     l = ifex_ite (restrict_top i x True) (restrict_top t x True) (restrict_top e x True);
     r = ifex_ite (restrict_top i x False) (restrict_top t x False) (restrict_top e x False) in
                        if l = r then l else IF x l r)"
by pat_completeness auto

declare Let_def[simp]

lemma restrict_size_le: "size (restrict_top k x val) \<le> size k"
by(induction k) (auto)

lemma restrict_size_element: "var \<in> ifex_top_var_set k \<Longrightarrow>
                                   size (restrict_top k var val) < size k"
by(induction k) (auto)

lemma ifex_top_var_set_finite: "finite (ifex_top_var_set k)"
  by (induction k) auto

lemma termlemma2:
  assumes "var = Min (\<Union>(ifex_top_var_set ` {(IF iv it ie), t, e}))"
  shows
  "(size (restrict_top (IF iv it ie) var val) +
    size (restrict_top t var val) +
    size (restrict_top e var val))
    < (size (IF iv it ie) + size t + size e)"
proof -
  from assms have "(\<Union>(ifex_top_var_set ` {(IF iv it ie), t, e})) \<noteq> {}"
                  "finite (\<Union>(ifex_top_var_set ` {(IF iv it ie), t, e}))"
    using ifex_top_var_set_finite by fastforce+
  from Min_in[OF this(2) this(1)] assms have "var \<in> (\<Union>(ifex_top_var_set ` {(IF iv it ie), t, e}))"
    by fast
  from this have var_elem: "var \<in> ifex_top_var_set (IF iv it ie) \<or>
                            var \<in> ifex_top_var_set t \<or>
                            var \<in> ifex_top_var_set e"
    by blast
  from this show ?thesis
proof(rule disjE)
  case goal1 then have
    "size (restrict_top (IF iv it ie) var val) < size (IF iv it ie)"
    "size (restrict_top t var val) + size (restrict_top e var val) \<le> size t + size e"
    by(simp add: restrict_size_le add_le_mono)+
  from this show ?thesis by linarith
  next
  case goal2 then show ?thesis
  proof(rule disjE)
    case goal1 then have 0: "size (restrict_top t var val) < size t"
        using restrict_size_element by fastforce
      have "size (restrict_top (IF iv it ie) var val) + size (restrict_top e var val) \<le>
            size (IF iv it ie) + size e" by (meson restrict_size_le add_le_mono)
      with 0 show ?thesis by linarith
    next
    case goal2 then have 0: "size (restrict_top e var val) < size e"
        using restrict_size_element by fastforce
      have "size (restrict_top (IF iv it ie) var val) + size (restrict_top t var val) \<le>
            size (IF iv it ie) + size t" by (meson restrict_size_le add_le_mono)
      with 0 show ?thesis by linarith
    qed
  qed
qed

lemma termlemma: "xa = Min (\<Union>(ifex_top_var_set ` {(IF iv it ie), t, e})) \<Longrightarrow>
       (case (restrict_top (IF iv it ie) xa val, restrict_top t xa val, restrict_top e xa val)
             of (i, t, e) \<Rightarrow> size i + size t + size e) < (case (IF iv it ie, t, e)
             of (i, t, e) \<Rightarrow> size i + size t + size e)"
using termlemma2 by fast

termination ifex_ite
  by (relation "measure (\<lambda>(i,t,e). size i + size t + size e)", rule wf_measure, unfold in_measure)
     (simp_all only: termlemma)+


(* INDUCTIVE DEFINITION *)

abbreviation ifex_variables_ite where
  "ifex_variables_ite i t e \<equiv>
   ifex_var_set i \<union> ifex_var_set t \<union> ifex_var_set e"

inductive ind_ite :: "('a::linorder) ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> bool" where
ind_ite_true:   "ind_ite t Trueif t e" |
ind_ite_false:  "ind_ite e Falseif t e" |
ind_ite_if:     "x = Min (\<Union>(ifex_top_var_set ` {i,t,e})) \<Longrightarrow>
   i = IF iv tifex eifex \<Longrightarrow>
   ind_ite l (restrict_top i x True) (restrict_top t x True) (restrict_top e x True) \<Longrightarrow>
   ind_ite r (restrict_top i x False) (restrict_top t x False) (restrict_top e x False) \<Longrightarrow>
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
          y_def: "y = Min (\<Union>(ifex_top_var_set ` {i,t,e}))" and
          r_def: "r = ifex_ite (restrict_top i y False) (restrict_top t y False)
                               (restrict_top e y False)" and
          l_def: "l = ifex_ite (restrict_top i y True) (restrict_top t y True)
                               (restrict_top e y True)" by simp
  from this ifex_ite_IF(1)[of i y l]  ifex_ite_IF(2)[of i y l r]
    have landr: "ind_ite l (restrict_top i y True) (restrict_top t y True)
                           (restrict_top e y True)"
                "ind_ite r (restrict_top i y False) (restrict_top t y False)
                           (restrict_top e y False)" by auto
  from ifex_ite_IF(3) l_def r_def y_def i_def have "b = (if l = r then l else IF y l r)" by force
  with ind_ite_if[OF y_def i_def landr] show ?case using i_def by simp
qed (auto simp add: ind_ite.intros)
next
assume "ind_ite b i t e" thus "ifex_ite i t e = b"
proof(induction rule: ind_ite.induct)
qed (auto)
qed

lemma restrict_top_variables_subset: "ifex_var_set (restrict_top k var val) \<subseteq> ifex_var_set k"
  by (induction k) (auto)


end

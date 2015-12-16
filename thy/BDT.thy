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

abbreviation ifex_robdt where
  "ifex_robdt t \<equiv> ifex_ordered t \<and> ifex_minimal t"

lemma "ifex_robdt x \<Longrightarrow> ifex_robdt y \<Longrightarrow> \<forall>ass. val_ifex x ass = val_ifex y ass \<Longrightarrow> x = y"
  oops

lemma "single_valued ifex_bf2_rel"
  oops

end

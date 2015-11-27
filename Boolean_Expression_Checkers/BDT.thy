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
  "ordner (IF v t e) = ((\<forall>tv \<in> ifex_variable_set t. v < tv) \<and> (\<forall>ev \<in> ifex_variable_set t. v < ev)
                       \<and> ordner t \<and> ordner e)" |
  "ordner Trueif = True" |
  "ordner Falseif = True"

definition ifex_bf2_rel where
  "ifex_bf2_rel = {(a,b). (\<forall>ass. a ass \<longleftrightarrow> val_ifex b ass) \<and> ordner b}"

definition select where "select a = undefined"

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

lemma restrict_assignment: "val_ifex b (ass(var := val)) = val_ifex (restrict b var val) ass"
  by (induction b) auto

lemma restrict_variables_subset: "ifex_variable_set (restrict b var val) \<subseteq> ifex_variable_set b"
  by (induction b) auto

lemma restrict_ordner_invar: "ordner b \<Longrightarrow> ordner (restrict b var val)"
  apply (induction b arbitrary: b') using restrict_variables_subset by (fastforce)+

lemma restrict_val_invar: "\<forall>ass. a ass = val_ifex b ass \<Longrightarrow> 
      (bf2_restrict var val a) ass = val_ifex (restrict b var val) ass"
  unfolding bf2_restrict_def using restrict_assignment by simp

lemma restrict_ifex_bf2_rel: 
"(a, b) \<in> ifex_bf2_rel \<Longrightarrow> (bf2_restrict var val a, restrict b var val) \<in> ifex_bf2_rel"
  unfolding ifex_bf2_rel_def using restrict_ordner_invar restrict_val_invar by auto

function dings :: "'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex" where
  "dings Trueif t e = t" |
  "dings Falseif t e = e" |
  "dings (IF iv it ie) t e = (let i = (IF iv it ie); x = select (ifex_variable_set ` {i,t,e}) in 
                         (IF x (dings (restrict i x True) (restrict t x True) (restrict e x True))
                               (dings (restrict i x False) (restrict t x False) (restrict e x False))))"
by pat_completeness auto

lemma "x \<in> ifex_variable_set k \<Longrightarrow> size (restrict k x val) < size k"

termination dings
apply(relation "measure size", rule wf_measure)


end
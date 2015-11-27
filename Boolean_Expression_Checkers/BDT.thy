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
  "ordner (IF v t e) = ((\<forall>tv \<in> ifex_variable_set t. v < tv) \<and> (\<forall>ev \<in> ifex_variable_set t. v < ev))" |
  "ordner Trueif = True" |
  "ordner Falseif = True"


definition ifex_bf2_rel where
  "ifex_bf2_rel = {(a,b) | a b. \<forall>ass. a ass \<longleftrightarrow> val_ifex b ass \<and> ordner b}"

definition select where "select a = undefined"

fun restrict where
  "restrict (IF v t e) var val = (if v = var then restrict (if val then t else e) var val else (IF v (restrict t var val) (restrict e var val)))" |
  "restrict i _ _ = i"

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
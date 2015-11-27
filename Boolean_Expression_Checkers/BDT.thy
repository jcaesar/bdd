theory BDT
imports Boolean_Expression_Checkers
        "../ibdd/thy/BoolFunc"
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

fun restrict_true where
  "restrict_true (IF v t e) var = (if v = var then t else (IF v t e))" |
  "restrict_true i _ = i"

fun restrict_false where
  "restrict_false (IF v t e) var = (if v = var then e else (IF v t e))" |
  "restrict_false i _ = i"

function dings :: "'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex" where
  "dings Trueif t e = t" |
  "dings Falseif t e = e" |
  "dings i t e = (let x = select (ifex_variable_set ` {i,t,e}) in 
                         (IF x (dings (restrict_true i x) (restrict_true t x) (restrict_true e x))
                               (dings (restrict_false i x) (restrict_false t x) (restrict_false e x))))"
by pat_completeness auto



end
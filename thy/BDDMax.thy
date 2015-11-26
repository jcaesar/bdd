theory BDDMax
imports Main
begin



datatype 'a AROBDD = FalseSink | TrueSink | UniqueNode 'a "'a AROBDD" "'a AROBDD"

context linorder
begin

fun AROBDD_name :: "'a AROBDD \<Rightarrow> 'a option" where
  "AROBDD_name (UniqueNode v _ _) = Some v" |
  "AROBDD_name FalseSink = None" |
  "AROBDD_name TrueSink = None"

fun AROBDD_nodes :: "'a AROBDD \<Rightarrow> 'a set" where
  "AROBDD_nodes (UniqueNode v l r) = {v} \<union> (AROBDD_nodes l) \<union> (AROBDD_nodes r)" |
  "AROBDD_nodes FalseSink = {}" |
  "AROBDD_nodes TrueSink = {}"

fun AROBDD_ordered :: "'a AROBDD \<Rightarrow> bool" where
  "AROBDD_ordered (UniqueNode v l r) = ((\<forall>ln \<in> AROBDD_nodes l. ln < v) \<and> 
                                         (\<forall>rn \<in> AROBDD_nodes r. rn < v))" |
  "AROBDD_ordered FalseSink = True" |
  "AROBDD_ordered TrueSink = True"

(* Keine Ahnung, wie ich linorder auf 'b bekomme. Man könnte auch 'a nochmal verwenden *)
(* Und dann noch ('b \<Rightarrow> bool) für das richtige variablen mapping *)

definition nodename_to_boolvar_map_restrict :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "dings f \<equiv> a < b \<Longrightarrow> f a < f b"

end
end
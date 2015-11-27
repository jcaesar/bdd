theory BDDMax
imports Main
begin


datatype 'a AROBDD_uname = FalseSinkName | TrueSinkName | UniqueNodeName 'a

datatype 'a AROBDD = FalseSink | TrueSink | UniqueNode "'a AROBDD_uname" "'a AROBDD" "'a AROBDD"

context linorder
begin

fun AROBDD_name :: "'a AROBDD \<Rightarrow> 'a AROBDD_uname" where
  "AROBDD_name (UniqueNode v _ _) = v" |
  "AROBDD_name FalseSink = FalseSinkName" |
  "AROBDD_name TrueSink = TrueSinkName"

fun AROBDD_nodes :: "'a AROBDD \<Rightarrow> 'a AROBDD_uname set" where
  "AROBDD_nodes (UniqueNode v l r) = {v} \<union> (AROBDD_nodes l) \<union> (AROBDD_nodes r)" |
  "AROBDD_nodes FalseSink = {}" |
  "AROBDD_nodes TrueSink = {}"

(* Maybe use option *)
fun AROBDD_uname_set :: "'a AROBDD_uname \<Rightarrow> 'a set" where
  "AROBDD_uname_set (UniqueNodeName v) = {v}" |
  "AROBDD_uname_set FalseSinkName = {}" |
  "AROBDD_uname_set TrueSinkName = {}"

fun AROBDD_nodes_names :: "'a AROBDD \<Rightarrow> 'a set" where
  "AROBDD_nodes_names (UniqueNode v l r) = AROBDD_uname_set v \<union> (AROBDD_nodes_names l) 
                                           \<union> (AROBDD_nodes_names r)" |
  "AROBDD_nodes_names FalseSink = {}" |
  "AROBDD_nodes_names TrueSink = {}"

end
end
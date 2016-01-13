theory Conc_Impl
imports TestImpl1 
  "$AFP/Separation_Logic_Imperative_HOL/Sep_Main"
  "$AFP/Separation_Logic_Imperative_HOL/Examples/Hash_Map_Impl"
  "$AFP/Separation_Logic_Imperative_HOL/Examples/Array_Blit"
  ArrayList
begin

  record bdd_impl =
    nodesi :: "(nat\<times>nat\<times>nat) array_list"
    lunodei :: "((nat\<times>nat\<times>nat),nat) hashtable"

  definition is_bdd_impl :: "bdd \<Rightarrow> bdd_impl \<Rightarrow> assn" where
    "is_bdd_impl b bi \<equiv> 
      is_array_list (nodes b) (nodesi bi) 
    * is_hashmap (lunode b) (lunodei bi)"

  lemma "precise is_bdd_impl" 
    sorry

  definition init_bdd_impl :: "bdd_impl" where
    "init_bdd_impl \<equiv> do {
      


    }"   



end

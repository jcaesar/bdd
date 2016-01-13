theory PointerMapImpl
imports ArrayList 
  "$AFP/Separation_Logic_Imperative_HOL/Sep_Main"
  "$AFP/Separation_Logic_Imperative_HOL/Examples/Hash_Map_Impl"
  PointerMap
begin

  record 'a pointer_map_impl =
    entriesi :: "'a array_list"
    getentryi :: "('a,nat) hashtable"

  definition is_pointer_map_impl where
    "is_pointer_map_impl b bi \<equiv> 
      is_array_list (entries b) (entriesi bi) 
    * is_hashmap (getentry b) (getentryi bi)"

  lemma "precise is_pointer_map_impl"
  	unfolding is_pointer_map_impl_def[abs_def]
  	apply(rule preciseI)
  	using preciseD[OF is_array_list_prec] preciseD[OF is_hashmap_prec]
  	apply- 
  	find_theorems "_ \<Turnstile> _ * _"
    sorry

  definition init_bdd_impl :: "bdd_impl" where
    "init_bdd_impl \<equiv> do {
      


    }"   



end

theory PointerMapImpl
imports ArrayList 
  "$AFP/Separation_Logic_Imperative_HOL/Sep_Main"
  "$AFP/Separation_Logic_Imperative_HOL/Examples/Hash_Map_Impl"
  PointerMap
begin

  record 'a pointermap_impl =
    entriesi :: "'a array_list"
    getentryi :: "('a,nat) hashtable"

  definition is_pointermap_impl where
    "is_pointermap_impl b bi \<equiv> 
      is_array_list (entries b) (entriesi bi) 
    * is_hashmap (getentry b) (getentryi bi)"

  lemma "precise is_pointermap_impl"
  	unfolding is_pointermap_impl_def[abs_def]
  	apply(rule preciseI)
  	apply(auto)
  	using preciseD[OF is_array_list_prec] preciseD[OF is_hashmap_prec]
  	unfolding mod_and_dist 
  	find_theorems "_ \<Turnstile> _ * _"
    sorry

  definition pointermap_empty where
    "pointermap_empty \<equiv> do {
      hm \<leftarrow> hm_new;
      arl \<leftarrow> arl_empty;
      return \<lparr>entriesi = arl, getentryi = hm \<rparr>
    }"

  lemma [sep_heap_rules]: "< emp > pointermap_empty <is_pointermap_impl empty_pointermap>\<^sub>t"
    by (sep_auto simp: pointermap_empty_def empty_pointermap_def is_pointermap_impl_def)

  definition pm_pthi where
    "pm_pthi m p \<equiv> arl_nth (entriesi m) p"

  lemma [sep_heap_rules]: "pointermap_p_valid p m \<Longrightarrow> < is_pointermap_impl m mi > pm_pthi mi p <\<lambda>ai. \<up>(ai = pm_pth m p)>\<^sub>t"
    by (sep_auto simp: pm_pthi_def pm_pth_def is_pointermap_impl_def pointermap_p_valid_def)

  definition pointermap_getmki where
    "pointermap_getmki a m \<equiv> do {
        lo \<leftarrow> ht_lookup a (getentryi m);
        (case lo of 
        	Some l \<Rightarrow> return (l,m) | 
        	None \<Rightarrow> do {
        		p \<leftarrow> return (snd (entriesi m));
				ent \<leftarrow> arl_append (entriesi m) a;
				lut \<leftarrow> hm_update a p (getentryi m);
				u \<leftarrow> return \<lparr>entriesi = ent, getentryi = lut\<rparr>;
				return (p,u)
        	}
        )
    }"
  lemma [sep_heap_rules]: "(p,u) = pointermap_getmk a m \<Longrightarrow> < is_pointermap_impl m mi > pointermap_getmki a mi <\<lambda>(pi,ui). is_pointermap_impl u ui * \<up>(pi = p)>\<^sub>t"
  unfolding pointermap_getmki_def pointermap_getmk_def pointermap_insert_def is_pointermap_impl_def
  	apply (sep_auto simp: pointermap_getmki_def pointermap_getmk_def pointermap_insert_def is_pointermap_impl_def ) 
  	apply(rename_tac b c d e f) (* no idea what they even are *)
  	apply(rule_tac x = "(e,f)" in is_array_list_lengthI)
  	find_theorems "_ \<Turnstile> _ * ?a \<Longrightarrow> _ \<Turnstile> ?a" (* how do I even separate? *)
    apply (sep_auto simp: pointermap_getmki_def pointermap_getmk_def pointermap_insert_def is_pointermap_impl_def is_array_list_def  intro: is_array_list_lengthI split: prod.splits)
    defer
    (* I quit for now *)
    defer
    oops
   
end

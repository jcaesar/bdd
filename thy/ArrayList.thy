(* Array implementation for list, contributed by Peter Lammich (except for the whacky parts) *)
theory ArrayList
imports
	"$AFP/Separation_Logic_Imperative_HOL/Examples/Array_Blit"
begin

  type_synonym 'a array_list = "'a array \<times> nat"

  definition "is_array_list l \<equiv> \<lambda>(a,n). \<exists>\<^sub>Al'. a \<mapsto>\<^sub>a l' * \<up>(n \<le> length l' \<and> l = take n l' \<and> length l'>0)"

  definition "initial_capacity \<equiv> 16::nat"

  definition "arl_empty \<equiv> do {
    a \<leftarrow> Array.new initial_capacity default;
    return (a,0)
  }"

  lemma [sep_heap_rules]: "< emp > arl_empty <is_array_list []>"
    by (sep_auto simp: arl_empty_def is_array_list_def initial_capacity_def)

  definition "arl_nth \<equiv> \<lambda>(a,n) i. do {
    Array.nth a i
  }"  

  lemma [sep_heap_rules]: "i<length l \<Longrightarrow> < is_array_list l a > arl_nth a i <\<lambda>x. is_array_list l a * \<up>(x = l!i) >"  
    by (sep_auto simp: arl_nth_def is_array_list_def split: prod.splits)

  definition "arl_append \<equiv> \<lambda>(a,n) x. do {
    len \<leftarrow> Array.len a;

    if n<len then do {
      a \<leftarrow> Array.upd n x a;
      return (a,n+1)
    } else do {
      let newcap = 2 * len;
      a \<leftarrow> array_grow a newcap default;
      a \<leftarrow> Array.upd n x a;
      return (a,n+1)
    }
  }"

  lemma [sep_heap_rules]: "
    < is_array_list l a > 
      arl_append a x 
    <\<lambda>a. is_array_list (l@[x]) a >\<^sub>t"  
    by (sep_auto 
      simp: arl_append_def is_array_list_def take_update_last neq_Nil_conv
      split: prod.splits nat.split)


end 
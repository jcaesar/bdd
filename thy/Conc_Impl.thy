theory Conc_Impl
imports PointerMapImpl TestImpl1
begin

instantiation prod :: (default, default) default
begin
	definition "default_prod :: ('a \<times> 'b) \<equiv> (default, default)" 
	instance by(intro_classes)
end
(* can be found in "~~/src/HOL/Proofs/Extraction/Greatest_Common_Divisor" or "~~/src/HOL/Proofs/Lambda/WeakNorm" *)
instantiation nat :: default
begin
	definition "default_nat \<equiv> 0 :: nat"
	instance ..
end

definition "tci bdd \<equiv> return (1,bdd)"
definition "fci bdd \<equiv> return (0,bdd)"
definition "ifci v t e bdd \<equiv> (if t = e then return (t, bdd) else do {
	(p,u) \<leftarrow> pointermap_getmki (v, t, e) bdd;
	return (Suc (Suc p), u)
})"

lemma [sep_heap_rules]: "<is_pointermap_impl bdd bddi> tci bddi <\<lambda>r. is_pointermap_impl bdd (snd r) * \<up>(fst r = fst (tmi bdd))>"
by(sep_auto simp: tci_def)
lemma [sep_heap_rules]: "<is_pointermap_impl bdd bddi> fci bddi <\<lambda>r. is_pointermap_impl bdd (snd r) * \<up>(fst r = fst (fmi bdd))>"
by(sep_auto simp: fci_def)
lemma [sep_heap_rules]: "(p, u) = ifmi v t e bdd \<Longrightarrow>
	<is_pointermap_impl bdd bddi> ifci v t e bddi
	<\<lambda>(pi,ui). is_pointermap_impl u ui * \<up>(pi = p)>\<^sub>t"
by(sep_auto simp: ifci_def apfst_def map_prod_def split: prod.splits if_splits)


end

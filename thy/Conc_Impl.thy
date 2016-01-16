theory Conc_Impl
imports PointerMapImpl TestImpl1
begin

datatype nat_trip = NatTrip (tfst: nat) (tsnd: nat) (ttrd: nat)
(*type_synonym nat_trip = "(nat \<times> nat \<times> nat)" Instance won't eat this.*)
term hashcode
instantiation nat_trip :: default
begin
	definition "default_nat_trip \<equiv> NatTrip 0 0 0"
	instance ..
end
instantiation nat_trip :: hashable
begin
  definition "hashcode_nat_trip x \<equiv> (hashcode (tfst x) * 33 + hashcode (tsnd x)) * 33 + hashcode (tsnd x)"
  definition "def_hashmap_size = (\<lambda>_ :: nat_trip itself. def_hashmap_size TYPE(nat) * 2)"
  instance using def_hashmap_size[where ?'a=nat] def_hashmap_size[where ?'a=nat]
    by(intro_classes)(simp_all add: def_hashmap_size_nat_trip_def)
end
instantiation nat_trip :: heap
begin
	instance proof(intro_classes)
		have "\<exists>(f::(nat \<times> nat) \<Rightarrow> nat). inj f" by (simp add: ex_inj)
		then guess f ..
		note injf = this
		hence "inj (\<lambda>nt. f (f (tfst nt, tsnd nt), ttrd nt))"
			apply -
			apply(rule injI)
			apply(simp add: inj_eq nat_trip.expand)
		done
		thus "\<exists>(g::nat_trip \<Rightarrow> nat). inj g" by auto
	qed
end


definition "tci bdd \<equiv> return (1,bdd)"
definition "fci bdd \<equiv> return (0,bdd)"
definition "ifci v t e bdd \<equiv> do {
	(p,u) \<leftarrow> pointermap_getmki (NatTrip v t e) bdd;
	return (Suc (Suc p), u)
}"

lemma [sep_heap_rules]: "<is_pointermap_impl bdd bddi> tci bddi <\<lambda>r. is_pointermap_impl bdd (snd r) * \<up>(fst r = fst (tmi bdd))>"
by(sep_auto simp: tci_def)
lemma [sep_heap_rules]: "<is_pointermap_impl bdd bddi> fci bddi <\<lambda>r. is_pointermap_impl bdd (snd r) * \<up>(fst r = fst (fmi bdd))>"
by(sep_auto simp: fci_def)
lemma [sep_heap_rules]: "<is_pointermap_impl bdd bddi> ifci v t e bddi
	<\<lambda>r. let (p,u) = ifmi v t e bdd in is_pointermap_impl bdd u * \<up>(fst r = p)>"
apply(sep_auto simp: ifci_def)


end

section{*Imparative implementation*}
theory Conc_Impl
imports PointerMapImpl AbstractInterpretation
begin

instantiation prod :: (default, default) default
begin
	definition "default_prod :: ('a \<times> 'b) \<equiv> (default, default)" 
	instance ..
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
definition destrci :: "nat \<Rightarrow> (nat \<times> nat \<times> nat) pointermap_impl \<Rightarrow> (nat, nat) IFEXD Heap" where
"destrci n bdd \<equiv> (case n of
	0 \<Rightarrow> return FD |
	Suc 0 \<Rightarrow> return TD |
	Suc (Suc p) \<Rightarrow> pm_pthi bdd p \<guillemotright>= (\<lambda>(v,t,e). return (IFD v t e)))"

lemma [sep_heap_rules]: "<is_pointermap_impl bdd bddi> tci bddi <\<lambda>r. is_pointermap_impl bdd (snd r) * \<up>(fst r = fst (tmi bdd))>"
by(sep_auto simp: tci_def)
lemma [sep_heap_rules]: "<is_pointermap_impl bdd bddi> fci bddi <\<lambda>r. is_pointermap_impl bdd (snd r) * \<up>(fst r = fst (fmi bdd))>"
by(sep_auto simp: fci_def)
lemma [sep_heap_rules]: "(p, u) = ifmi v t e bdd \<Longrightarrow>
	<is_pointermap_impl bdd bddi> ifci v t e bddi
	<\<lambda>(pi,ui). is_pointermap_impl u ui * \<up>(pi = p)>\<^sub>t"
by(sep_auto simp: ifci_def apfst_def map_prod_def split: prod.splits if_splits)
lemma [sep_heap_rules]: "
	n < 2 \<or> pointermap_p_valid (n - 2) bdd \<Longrightarrow>
	<is_pointermap_impl bdd bddi> destrci n bddi
	<\<lambda>r. is_pointermap_impl bdd bddi * \<up>(r = destrmi n bdd)>"
by(cases "(n, bdd)" rule: destrmi.cases) (sep_auto simp: destrci_def)+

definition "restrict_topci p var val bdd = do {
	d \<leftarrow> destrci p bdd;
	return (case d of IFD v t e \<Rightarrow> (if v = var then (if val then t else e) else p) | _ \<Rightarrow> p)
}"
lemma [sep_heap_rules]: "
	p < 2 \<or> pointermap_p_valid (p - 2) bdd \<Longrightarrow>
	<is_pointermap_impl bdd bddi> restrict_topci p var val bddi
	<\<lambda>r. is_pointermap_impl bdd bddi * \<up>(r = brofix.restrict_top_impl p var val bdd)>"
by(sep_auto simp: restrict_topci_def)

fun lowest_topsci where
"lowest_topsci [] s = return None" |
"lowest_topsci (e#es) s = 
	(if e < 2 then lowest_topsci es s else do {
		(c,_,_) \<leftarrow> pm_pthi s e;
		rec \<leftarrow> lowest_topsci es s;
		return (case rec of Some d \<Rightarrow> Some (min c d) | None \<Rightarrow> Some c)
	})"
term "(list_all (pointermap_p_valid\<inverse>\<inverse> bdd), bdd)" 
lemma [sep_heap_rules]: "
	list_all (\<lambda>e. e < 2 \<or> pointermap_p_valid (e - 2) bdd) es \<Longrightarrow>
	<is_pointermap_impl bdd bddi> lowest_topsci es bddi
	<\<lambda>r. is_pointermap_impl bdd bddi * \<up>(r = brofix.lowest_tops_impl es bdd)>"
apply(induction es)
apply(sep_auto simp:)
apply(sep_auto simp: split: IFEXD.splits) 
oops (* I doubt that sep_auto does induction. I'll check later, more pressing matters to attend. *)

(* partial_function(option) ite_impl_opt where
"ite_impl_opt i t e s =
  (case DESTRimpl i s of TD \<Rightarrow> Some (t,s) | FD \<Rightarrow> Some (e,s) | _ \<Rightarrow>
  (if DESTRimpl t s = TD \<and> DESTRimpl e s = FD then Some (i,s) else
  (if e = t then Some (t,s) else
	(case lowest_tops_impl [i, t, e] s of
		Some a \<Rightarrow> (let
			ti = restrict_top_impl i a True s;
			tt = restrict_top_impl t a True s;
			te = restrict_top_impl e a True s;
			fi = restrict_top_impl i a False s;
			ft = restrict_top_impl t a False s;
			fe = restrict_top_impl e a False s
			in do {
			(tb,s) \<leftarrow> ite_impl_opt ti tt te s;
			(fb,s) \<leftarrow> ite_impl_opt fi ft fe s;
            Some (IFimpl a tb fb s)}) |
        None \<Rightarrow> Some (case DESTRimpl i s of TD \<Rightarrow> (t, s) | FD \<Rightarrow> (e, s))))))"*)


end

section{*Imparative implementation*}
theory Conc_Impl
imports PointerMapImpl AbstractInterpretation
  "$AFP/Automatic_Refinement/Lib/Refine_Lib"
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

lemma [sep_heap_rules]: "tmi bdd = (p,bdd') 
  \<Longrightarrow> <is_pointermap_impl bdd bddi> 
        tci bddi 
      <\<lambda>(pi,bddi'). is_pointermap_impl bdd' bddi' * \<up>(pi = p)>"
by(sep_auto simp: tci_def)

lemma [sep_heap_rules]: "fmi bdd = (p,bdd') 
  \<Longrightarrow> <is_pointermap_impl bdd bddi> 
        fci bddi 
      <\<lambda>(pi,bddi'). is_pointermap_impl bdd' bddi' * \<up>(pi = p)>"
by(sep_auto simp: fci_def)

lemma [sep_heap_rules]: "\<lbrakk>(p, bdd') = ifmi v t e bdd; ti = t; ei = e \<rbrakk> \<Longrightarrow>
	<is_pointermap_impl bdd bddi> ifci v ti ei bddi
	<\<lambda>(pi,bddi'). is_pointermap_impl bdd' bddi' * \<up>(pi = p)>\<^sub>t"
by(sep_auto
  simp: ifci_def apfst_def map_prod_def
  split: prod.splits if_splits)

lemma [sep_heap_rules]: "
	bdd_node_valid bdd n \<Longrightarrow>
	bdd_sane bdd \<Longrightarrow>
	<is_pointermap_impl bdd bddi> destrci n bddi
	<\<lambda>r. is_pointermap_impl bdd bddi * \<up>(r = destrmi n bdd \<and> ifexd_valid bdd r)>"
	apply (subst is_pi_sane_subst; clarsimp)
	apply(cases "(n, bdd)" rule: destrmi.cases) 
	apply(sep_auto simp: destrci_def bdd_node_valid_def ifexd_valid_def)
	apply(sep_auto simp: destrci_def bdd_node_valid_def ifexd_valid_def)
	apply(clarify)
	apply(subst (asm) bdd_sane_def[of bdd])
	apply(clarify)
	apply(sep_auto simp: destrci_def)
	apply(sep_auto simp: destrci_def bdd_node_valid_def)
	apply(clarsimp split: prod.splits)
	apply(sep_auto)
done

definition "restrict_topci p var val bdd = do {
	d \<leftarrow> destrci p bdd;
	return (case d of IFD v t e \<Rightarrow> (if v = var then (if val then t else e) else p) | _ \<Rightarrow> p)
}"

thm brofix.restrict_top_R[THEN bdd_node_valid_RmiI]

lemma [sep_heap_rules]: "
	bdd_sane bdd \<Longrightarrow>
	bdd_node_valid bdd p \<Longrightarrow>
	<is_pointermap_impl bdd bddi> restrict_topci p var val bddi
	<\<lambda>r. is_pointermap_impl bdd bddi * \<up>(r = brofix.restrict_top_impl p var val bdd)>"
  by(sep_auto simp: restrict_topci_def ifexd_valid_def split split: IFEXD.splits)

fun lowest_topsci where
"lowest_topsci [] s = return None" |
"lowest_topsci (e#es) s = do {
		des \<leftarrow> destrci e s;
		rec \<leftarrow> lowest_topsci es s;
		return (case des of
			(IFD v t e) \<Rightarrow> (case rec of 
				Some u \<Rightarrow> Some (min u v) | 
				None \<Rightarrow> Some v) |
			_ \<Rightarrow> rec)
	}"

lemma [sep_heap_rules]: "
	bdd_sane bdd \<Longrightarrow>
	list_all (bdd_node_valid bdd) es \<Longrightarrow>
	<is_pointermap_impl bdd bddi> lowest_topsci es bddi
	<\<lambda>r. is_pointermap_impl bdd bddi * \<up>(r = brofix.lowest_tops_impl es bdd)>"
by(induction es) (sep_auto simp:)+

partial_function(heap) iteci where
"iteci i t e s = do {
  lt \<leftarrow> lowest_topsci [i, t, e] s;
  case lt of
		Some a \<Rightarrow> do {
			ti \<leftarrow> restrict_topci i a True s;
			tt \<leftarrow> restrict_topci t a True s;
			te \<leftarrow> restrict_topci e a True s;
			fi \<leftarrow> restrict_topci i a False s;
			ft \<leftarrow> restrict_topci t a False s;
			fe \<leftarrow> restrict_topci e a False s;
			(tb,s) \<leftarrow> iteci ti tt te s;
			(fb,s) \<leftarrow> iteci fi ft fe s;
      (ifci a tb fb s)
     } 
  | None \<Rightarrow> do {
    d \<leftarrow> destrci i s;
    case d of
      TD \<Rightarrow> return (t,s)
    | FD \<Rightarrow> return (e,s)
   }
  }"

(*
	Just noticed that in the current state, the destr-operator has to be called multiple times for each object.
	Let's not go all premature optimization on this though.
*)

lemma "
  ( bdd_sane bdd
  \<and> brofix.ite_impl i t e bdd = Some (p,bdd') 
  \<and> bdd_node_valid bdd i
  \<and> bdd_node_valid bdd t
  \<and> bdd_node_valid bdd e
  ) \<longrightarrow>
  <is_pointermap_impl bdd bddi> 
    iteci i t e bddi 
  <\<lambda>(pi,bddi'). is_pointermap_impl bdd' bddi' * \<up>(pi=p)>\<^sub>t"
proof (induction arbitrary: i t e bddi bdd p bdd' rule: brofix.ite_impl.fixp_induct)
	case 2 thus ?case by simp
next
	case (3 s)
	note [simp del] = destrmi.simps lowest_topsci.simps
		brofix.lowest_tops_impl.simps
		brofix.restrict_top_impl.simps
		ifmi.simps
	note [sep_heap_rules] = 3[THEN mp, OF conjI, OF _ conjI, OF _ _ conjI, OF _ _ _ conjI]
  show ?case
    apply (subst iteci.simps)
    apply (sep_auto)
    apply (split IFEXD.split option.splits; intro impI conjI; clarsimp) []
    apply sep_auto
    apply sep_auto

    apply (clarsimp split: Option.bind_splits)
    apply sep_auto
    prefer 4
    apply sep_auto
    prefer 6
    apply sep_auto
    prefer 4
    apply sep_auto
    sorry
next    
    case 1 thus ?case apply(clarsimp) find_theorems "ccpo.admissible" sorry
qed

end

section{*Imparative implementation*}
theory Conc_Impl
imports PointerMapImpl AbstractInterpretation
  (*"$AFP/Automatic_Refinement/Lib/Refine_Lib"*)
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

definition "is_bdd_impl bdd bddi = is_pointermap_impl bdd bddi"

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
  \<Longrightarrow> <is_bdd_impl bdd bddi> 
        tci bddi 
      <\<lambda>(pi,bddi'). is_bdd_impl bdd' bddi' * \<up>(pi = p)>"
by(sep_auto simp: tci_def)

lemma [sep_heap_rules]: "fmi bdd = (p,bdd') 
  \<Longrightarrow> <is_bdd_impl bdd bddi> 
        fci bddi 
      <\<lambda>(pi,bddi'). is_bdd_impl bdd' bddi' * \<up>(pi = p)>"
by(sep_auto simp: fci_def)

lemma [sep_heap_rules]: "\<lbrakk>bdd_sane bdd; ifmi v t e bdd = (p, bdd'); bdd_node_valid bdd t; bdd_node_valid bdd e \<rbrakk> \<Longrightarrow>
	<is_bdd_impl bdd bddi> ifci v t e bddi
	<\<lambda>(pi,bddi'). is_bdd_impl bdd' bddi' * \<up>(pi = p)>\<^sub>t"
	apply(clarsimp simp: is_bdd_impl_def simp del: ifmi.simps)
	apply(sep_auto
	  simp: ifci_def apfst_def map_prod_def is_bdd_impl_def bdd_sane_def
	  split: prod.splits if_splits)
done

lemma [sep_heap_rules]: "
	bdd_sane bdd \<Longrightarrow>
	bdd_node_valid bdd n \<Longrightarrow>
	<is_bdd_impl bdd bddi> destrci n bddi
	<\<lambda>r. is_bdd_impl bdd bddi * \<up>(r = destrmi n bdd)>" 
	apply(cases "(n, bdd)" rule: destrmi.cases)
	apply(sep_auto simp: destrci_def bdd_node_valid_def is_bdd_impl_def ifexd_valid_def bdd_sane_def dest: p_valid_RmiI)+
done

definition "restrict_topci p var val bdd = do {
	d \<leftarrow> destrci p bdd;
	return (case d of IFD v t e \<Rightarrow> (if v = var then (if val then t else e) else p) | _ \<Rightarrow> p)
}"

lemma [sep_heap_rules]: "
	bdd_sane bdd \<Longrightarrow>
	bdd_node_valid bdd p \<Longrightarrow>
	brofix.restrict_top_impl p var val bdd = Some r \<Longrightarrow>
	<is_bdd_impl bdd bddi> restrict_topci p var val bddi
	<\<lambda>ri. is_bdd_impl bdd bddi * \<up>(ri = r)>"
  by(sep_auto simp: restrict_topci_def ifexd_valid_def split split: IFEXD.splits Option.bind_splits)

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
	brofix.lowest_tops_impl es bdd = Some r \<Longrightarrow>
	<is_bdd_impl bdd bddi> lowest_topsci es bddi
	<\<lambda>ri. is_bdd_impl bdd bddi * \<up>(ri = r)>"
proof(induction es arbitrary: r)
	case Nil thus ?case by sep_auto
next
	case (Cons e es)
	thus ?case
	proof(cases "brofix.lowest_tops_impl es bdd")
		case None
		thus ?thesis using Cons.prems by(sep_auto)
	next
		case (Some rec)
		note [sep_heap_rules] = Cons.IH[OF Some]
		show ?thesis using Cons.prems Some 
			by(sep_auto split: Option.bind_splits dest: n_valid_RmiI)
	qed
qed


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
  <is_bdd_impl bdd bddi> 
    iteci i t e bddi 
  <\<lambda>(pi,bddi'). is_bdd_impl bdd' bddi' * \<up>(pi=p)>\<^sub>t"
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
    apply (sep_auto split: Option.bind_splits)
    using bdd_node_valid_def apply blast+
    apply (sep_auto split: Option.bind_splits)
    apply (clarsimp split: IFEXD.splits)
    (* NOOOOPE *)
    oops
    prefer 4
    apply (sep_auto split: Option.bind_splits)
    prefer 10 
    apply (sep_auto split: Option.bind_splits split: IFEXD.splits)
    prefer 5
    apply (sep_auto split: Option.bind_splits)
    prefer 4
    apply (sep_auto split: Option.bind_splits)
    proof -
    	case goal1 thus ?case
    
next    
    case 1 thus ?case apply(clarsimp) sorry
qed

end

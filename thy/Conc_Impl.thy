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

definition "bdd_node_valid bdd n \<equiv> n < 2 \<or> pointermap_p_valid (n - 2) bdd"

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

lemma "(42,1)\<in>{(v,v). v=1}" by simp

definition "node_rel bdd \<equiv> {(v,v) | v. bdd_node_valid bdd v}"

lemma [sep_heap_rules]: "tmi bdd = (p,bdd') 
  \<Longrightarrow> <is_pointermap_impl bdd bddi> 
        tci bddi 
      <\<lambda>(pi,bddi'). is_pointermap_impl bdd' bddi' * \<up>((pi,p)\<in>node_rel bdd')>"
by(sep_auto simp: tci_def node_rel_def bdd_node_valid_def)

lemma [sep_heap_rules]: "fmi bdd = (p,bdd') 
  \<Longrightarrow> <is_pointermap_impl bdd bddi> 
        fci bddi 
      <\<lambda>(pi,bddi'). is_pointermap_impl bdd' bddi' * \<up>((pi,p)\<in>node_rel bdd')>"
by(sep_auto simp: fci_def node_rel_def bdd_node_valid_def)

lemma [sep_heap_rules]: "\<lbrakk>(p, bdd') = ifmi v t e bdd; (ti,t)\<in>node_rel bdd; (ei,e)\<in>node_rel bdd \<rbrakk> \<Longrightarrow>
	<is_pointermap_impl bdd bddi> ifci v ti ei bddi
	<\<lambda>(pi,bddi'). is_pointermap_impl bdd' bddi' * \<up>((pi,p)\<in>node_rel bdd')>\<^sub>t"
by(sep_auto 
  simp: ifci_def apfst_def map_prod_def node_rel_def bdd_node_valid_def
  split: prod.splits if_splits)

lemma [sep_heap_rules]: "
	bdd_node_valid bdd n \<Longrightarrow>
	<is_pointermap_impl bdd bddi> destrci n bddi
	<\<lambda>r. is_pointermap_impl bdd bddi * \<up>(r = destrmi n bdd)>"
by(cases "(n, bdd)" rule: destrmi.cases) (sep_auto simp: destrci_def bdd_node_valid_def)+

lemma [simp]: 
  "bdd_node_valid bdd 0"
  "bdd_node_valid bdd (Suc 0)"
  by (auto simp: bdd_node_valid_def)

lemma bdd_node_valid_RmiI: "(ni,n)\<in>Rmi bdd \<Longrightarrow> bdd_node_valid bdd ni"
  apply (auto simp: Rmi_def)
  apply (cases "(ni,n,bdd)" rule: Rmi_g.cases; simp)
  apply (auto simp: bdd_node_valid_def)
  done

definition "restrict_topci p var val bdd = do {
	d \<leftarrow> destrci p bdd;
	return (case d of IFD v t e \<Rightarrow> (if v = var then (if val then t else e) else p) | _ \<Rightarrow> p)
}"

thm brofix.restrict_top_R[THEN bdd_node_valid_RmiI]

lemma [sep_heap_rules]: "
	bdd_node_valid bdd p \<Longrightarrow>
	<is_pointermap_impl bdd bddi> restrict_topci p var val bddi
	<\<lambda>r. is_pointermap_impl bdd bddi * \<up>((r, brofix.restrict_top_impl p var val bdd) \<in> node_rel bdd)>"
	unfolding node_rel_def apply (simp del: brofix.restrict_top_impl.simps)

  by(sep_auto simp: restrict_topci_def)

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

lemma "(brofix.ite_impl i t e bdd = Some (p,bdd') 
  \<and> bdd_node_valid bdd i
  \<and> bdd_node_valid bdd t
  \<and> bdd_node_valid bdd e
  ) \<longrightarrow>
  <is_pointermap_impl bdd bddi> 
    iteci i t e bddi 
  <\<lambda>(pi,bddi'). is_pointermap_impl bdd' bddi' * \<up>(pi=p)>"
proof -
  note [simp del] = destrmi.simps lowest_topsci.simps
    brofix.lowest_tops_impl.simps
    brofix.restrict_top_impl.simps
  show ?thesis
    apply (induction arbitrary: i t e bddi bdd p bdd' rule: brofix.ite_impl.fixp_induct)
    defer
    apply simp
    apply (subst iteci.simps)
    apply (sep_auto)
    apply (split IFEXD.split option.splits; intro impI conjI; clarsimp) []
    apply sep_auto
    apply sep_auto

    apply (clarsimp split: Option.bind_splits)
    apply sep_auto
    apply (simp only: atomize_imp[symmetric] conj_imp_eq_imp_imp)
    apply rprems
    apply assumption
    apply simp


qed

term brofix.ite_impl

context bdd_impl begin
thm iteci_def
thm ite_impl.fixp_induct


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

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

lemma [sep_heap_rules]: "tmi' bdd = Some (p,bdd') 
  \<Longrightarrow> <is_bdd_impl bdd bddi> 
        tci bddi 
      <\<lambda>(pi,bddi'). is_bdd_impl bdd' bddi' * \<up>(pi = p)>"
  by (sep_auto simp: tci_def tmi'_def split: Option.bind_splits)

lemma [sep_heap_rules]: "fmi' bdd = Some (p,bdd') 
  \<Longrightarrow> <is_bdd_impl bdd bddi> 
        fci bddi 
      <\<lambda>(pi,bddi'). is_bdd_impl bdd' bddi' * \<up>(pi = p)>"
by(sep_auto simp: fci_def fmi'_def split: Option.bind_splits)

lemma [sep_heap_rules]: "ifmi' v t e bdd = Some (p, bdd') \<Longrightarrow>
	<is_bdd_impl bdd bddi> ifci v t e bddi
	<\<lambda>(pi,bddi'). is_bdd_impl bdd' bddi' * \<up>(pi = p)>\<^sub>t"
	apply(clarsimp simp: is_bdd_impl_def ifmi'_def simp del: ifmi.simps)
	apply(sep_auto
	  simp: ifci_def apfst_def map_prod_def is_bdd_impl_def bdd_sane_def
	  split: prod.splits if_splits Option.bind_splits)
done

lemma [sep_heap_rules]: "
	destrmi' n bdd = Some r \<Longrightarrow>
	<is_bdd_impl bdd bddi> destrci n bddi
	<\<lambda>r'. is_bdd_impl bdd bddi * \<up>(r' = r)>" 
	unfolding destrmi'_def
	apply (clarsimp split: Option.bind_splits)
	apply(cases "(n, bdd)" rule: destrmi.cases)
	apply(sep_auto simp: destrci_def bdd_node_valid_def is_bdd_impl_def ifexd_valid_def bdd_sane_def dest: p_valid_RmiI)+
done

term brofix.restrict_top_impl

thm brofix.case_ifexi_def

definition "case_ifexici fti ffi fii ni bddi \<equiv> do {
  dest \<leftarrow> destrci ni bddi;
  case dest of TD \<Rightarrow> fti | FD \<Rightarrow> ffi | IFD v ti ei \<Rightarrow> fii v ti ei
}"

lemma [sep_decon_rules]:
  assumes S: "brofix.case_ifexi fti ffi fii ni bdd = Some r"
  assumes [sep_heap_rules]: 
    "destrmi' ni bdd = Some TD \<Longrightarrow> fti bdd = Some r \<Longrightarrow> <is_bdd_impl bdd bddi> ftci <Q>"
    "destrmi' ni bdd = Some FD \<Longrightarrow> ffi bdd = Some r \<Longrightarrow> <is_bdd_impl bdd bddi> ffci <Q>"
    "\<And>v t e. destrmi' ni bdd = Some (IFD v t e) \<Longrightarrow> fii v t e bdd = Some r \<Longrightarrow> <is_bdd_impl bdd bddi> fici v t e <Q> "
  shows "<is_bdd_impl bdd bddi> case_ifexici ftci ffci fici ni bddi <Q>"
  using S
  unfolding brofix.case_ifexi_def 
  apply (clarsimp split: Option.bind_splits IFEXD.splits)
  apply (sep_auto simp: case_ifexici_def) 
  apply (sep_auto simp: case_ifexici_def) 
  apply (sep_auto simp: case_ifexici_def) 
  done


definition "restrict_topci p vr vl bdd = 
  case_ifexici
    (return p)
    (return p)
    (\<lambda>v te ee. return (if v = vr then (if vl then te else ee) else p))
    p bdd
	"

lemma [sep_heap_rules]:
	assumes "brofix.restrict_top_impl p var val bdd = Some (r,bdd')"
	shows "<is_bdd_impl bdd bddi> restrict_topci p var val bddi
        	<\<lambda>ri. is_bdd_impl bdd bddi * \<up>(ri = r)>"
    using assms    	
    unfolding brofix.restrict_top_impl_def restrict_topci_def
    by sep_auto

fun lowest_topsci where
"lowest_topsci [] s = return None" |
"lowest_topsci (e#es) s = 
	  case_ifexici 
	    (lowest_topsci es s) 
	    (lowest_topsci es s) 
	    (\<lambda>v t e. do {
	    (rec) \<leftarrow> lowest_topsci es s;
        (case rec of 
          Some u \<Rightarrow> return ((Some (min u v))) | 
          None \<Rightarrow> return ((Some v)))
       }) e s
   "

declare lowest_topsci.simps[simp del]

lemma [sep_heap_rules]: 
	assumes "brofix.lowest_tops_impl es bdd = Some (r,bdd')"
	shows "<is_bdd_impl bdd bddi> lowest_topsci es bddi
	<\<lambda>(ri). is_bdd_impl bdd bddi * \<up>(ri = r \<and> bdd'=bdd)>"
proof -
  note [simp] = lowest_topsci.simps brofix.lowest_tops_impl.simps

  show ?thesis using assms
	apply (induction es arbitrary: bdd r bdd' bddi)
	apply (sep_auto ) (* TODO: Have to split on destrmi'-cases manually, else sep-aut introduces schematic before case-split is done *)
	apply (clarsimp simp: brofix.case_ifexi_def split: Option.bind_splits IFEXD.splits)
	apply (sep_auto simp: brofix.case_ifexi_def)
	apply (sep_auto simp: brofix.case_ifexi_def)
	apply (sep_auto simp: brofix.case_ifexi_def)
	done
qed

partial_function(heap) iteci where
"iteci i t e s = do {
  (lt) \<leftarrow> lowest_topsci [i, t, e] s;
  case lt of
		Some a \<Rightarrow> do {
			ti \<leftarrow> restrict_topci i a True s;
			tt \<leftarrow> restrict_topci t a True s;
			te \<leftarrow> restrict_topci e a True s;
			fi \<leftarrow> restrict_topci i a False s;
			ft \<leftarrow> restrict_topci t a False s;
			fe \<leftarrow> restrict_topci e a False s;
			(tb,s') \<leftarrow> iteci ti tt te s;
			(fb,s'') \<leftarrow> iteci fi ft fe s';
      (ifci a tb fb s'')
     } 
  | None \<Rightarrow> do {
    case_ifexici (return (t,s)) (return (e,s)) (\<lambda>_ _ _. raise ''Cannot happen'') i s
   }
  }"

lemma aux_prod_compr: "(\<forall>x1 x2 x3 x4 r1 r2. f (((x1,x2),x3),x4) = Some (r1,r2) \<longrightarrow> P x1 x2 x3 x4 r1 r2) \<longleftrightarrow>
  (\<forall>x y. f x = Some y \<longrightarrow> (case (x,y) of ((((x1,x2),x3),x4),(r1,r2)) \<Rightarrow> P x1 x2 x3 x4 r1 r2))" by auto


lemma "
  ( brofix.ite_impl i t e bdd = Some (p,bdd'))  \<longrightarrow>
  <is_bdd_impl bdd bddi> 
    iteci i t e bddi 
  <\<lambda>(pi,bddi'). is_bdd_impl bdd' bddi' * \<up>(pi=p )>\<^sub>t"
  apply (induction arbitrary: i t e bddi bdd p bdd' rule: brofix.ite_impl.fixp_induct)
  defer
  apply simp
  apply clarify
  apply (clarsimp split: option.splits Option.bind_splits prod.splits)
  apply (subst iteci.simps)
  apply (sep_auto )

  apply (subst iteci.simps)
  apply (sep_auto )

  unfolding imp_to_meta
  apply rprems  
  apply simp
  apply sep_auto
  apply (rule fi_rule)
  apply rprems  
  apply simp
  apply frame_inference
  apply sep_auto

  apply simp  (* Warning: Dragons ahead! *)
  using option_admissible[where P=
    "\<lambda>(((x1,x2),x3),x4) (r1,r2). \<forall>bddi. 
      <is_bdd_impl x4 bddi> 
        iteci x1 x2 x3 bddi  
      <\<lambda>r. case r of (pi, bddi') \<Rightarrow> is_bdd_impl r2 bddi' * \<up> (pi = r1)>\<^sub>t"]
  apply auto
  apply (fo_rule subst[rotated])
  apply (assumption)
  apply auto
  done


end

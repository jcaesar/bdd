section\<open>Imparative implementation\<close>
theory Conc_Impl
imports Pointer_Map_Impl Middle_Impl
begin

record bddi =
  dpmi :: "(nat \<times> nat \<times> nat) pointermap_impl"
  dcli :: "((nat \<times> nat \<times> nat),nat) hashtable"
lemma bdd_exhaust: "dpm a = dpm b \<Longrightarrow> dcl a = dcl b \<Longrightarrow> a = (b :: bdd)" by simp

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

definition "is_bdd_impl (bdd::bdd) (bddi::bddi) = is_pointermap_impl (dpm bdd) (dpmi bddi) * is_hashmap (dcl bdd) (dcli bddi)"

lemma is_bdd_impl_prec: "precise is_bdd_impl"
  apply(rule preciseI)
  apply(unfold is_bdd_impl_def)
  apply(clarsimp)
  apply(rename_tac a a' x y p F F')
  apply(rule bdd_exhaust)
   apply(rule_tac p = "dpmi p" and h = "(x,y)" in preciseD[OF is_pointermap_impl_prec])
   apply(unfold star_aci(1))
   apply blast
  apply(rule_tac p = "dcli p" and h = "(x,y)" in preciseD[OF is_hashmap_prec])
  apply(unfold star_aci(2)[symmetric])
  apply(unfold star_aci(1)[symmetric]) (* black unfold magic *)
  apply(unfold star_aci(2)[symmetric])
  apply blast
  (* This proof is exactly the same as for pointermap. One could make a rule from it. *)
done

definition "emptyci :: bddi Heap \<equiv> do { ep \<leftarrow> pointermap_empty; ehm \<leftarrow> hm_new; return \<lparr>dpmi=ep, dcli=ehm\<rparr> }"
definition "tci bdd \<equiv> return (1::nat,bdd::bddi)"
definition "fci bdd \<equiv> return (0::nat,bdd::bddi)"
definition "ifci v t e bdd \<equiv> (if t = e then return (t, bdd) else do {
                              (p,u) \<leftarrow> pointermap_getmki (v, t, e) (dpmi bdd);
                              return (Suc (Suc p), dpmi_update (const u) bdd)
})"
definition destrci :: "nat \<Rightarrow> bddi \<Rightarrow> (nat, nat) IFEXD Heap" where
"destrci n bdd \<equiv> (case n of
  0 \<Rightarrow> return FD |
  Suc 0 \<Rightarrow> return TD |
  Suc (Suc p) \<Rightarrow> pm_pthi (dpmi bdd) p \<bind> (\<lambda>(v,t,e). return (IFD v t e)))"

term "mi.les"

lemma emptyci_rule[sep_heap_rules]: "<emp> emptyci <is_bdd_impl emptymi>\<^sub>t"
  by(sep_auto simp: is_bdd_impl_def emptyci_def emptymi_def)

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
  by (sep_auto simp: ifci_def apfst_def map_prod_def is_bdd_impl_def bdd_sane_def
               split: prod.splits if_splits Option.bind_splits)

lemma destrci_rule[sep_heap_rules]: "
  destrmi' n bdd = Some r \<Longrightarrow>
  <is_bdd_impl bdd bddi> destrci n bddi
  <\<lambda>r'. is_bdd_impl bdd bddi * \<up>(r' = r)>" 
  unfolding destrmi'_def apply (clarsimp split: Option.bind_splits)
  apply(cases "(n, bdd)" rule: destrmi.cases)
    by (sep_auto simp: destrci_def bdd_node_valid_def is_bdd_impl_def ifexd_valid_def bdd_sane_def
                 dest: p_valid_RmiI)+

term mi.restrict_top_impl

thm mi.case_ifexi_def

definition "case_ifexici fti ffi fii ni bddi \<equiv> do {
  dest \<leftarrow> destrci ni bddi;
  case dest of TD \<Rightarrow> fti | FD \<Rightarrow> ffi | IFD v ti ei \<Rightarrow> fii v ti ei
}"

lemma [sep_decon_rules]:
  assumes S: "mi.case_ifexi fti ffi fii ni bdd = Some r"
  assumes [sep_heap_rules]: 
    "destrmi' ni bdd = Some TD \<Longrightarrow> fti bdd = Some r \<Longrightarrow> <is_bdd_impl bdd bddi> ftci <Q>"
    "destrmi' ni bdd = Some FD \<Longrightarrow> ffi bdd = Some r \<Longrightarrow> <is_bdd_impl bdd bddi> ffci <Q>"
    "\<And>v t e. destrmi' ni bdd = Some (IFD v t e) \<Longrightarrow> fii v t e bdd = Some r
     \<Longrightarrow> <is_bdd_impl bdd bddi> fici v t e <Q> "
  shows "<is_bdd_impl bdd bddi> case_ifexici ftci ffci fici ni bddi <Q>"
  using S unfolding mi.case_ifexi_def apply (clarsimp split: Option.bind_splits IFEXD.splits)
  by (sep_auto simp: case_ifexici_def)+


definition "restrict_topci p vr vl bdd = 
  case_ifexici
    (return p)
    (return p)
    (\<lambda>v te ee. return (if v = vr then (if vl then te else ee) else p))
    p bdd"

lemma [sep_heap_rules]:
  assumes "mi.restrict_top_impl p var val bdd = Some (r,bdd')"
  shows "<is_bdd_impl bdd bddi> restrict_topci p var val bddi
          <\<lambda>ri. is_bdd_impl bdd bddi * \<up>(ri = r)>"
  using assms unfolding mi.restrict_top_impl_def restrict_topci_def by sep_auto

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
       }) e s"

declare lowest_topsci.simps[simp del]

lemma [sep_heap_rules]:
  assumes "mi.lowest_tops_impl es bdd = Some (r,bdd')"
  shows "<is_bdd_impl bdd bddi> lowest_topsci es bddi
  <\<lambda>(ri). is_bdd_impl bdd bddi * \<up>(ri = r \<and> bdd'=bdd)>"
proof -
  note [simp] = lowest_topsci.simps mi.lowest_tops_impl.simps
  show ?thesis using assms
    apply (induction es arbitrary: bdd r bdd' bddi)
     apply (sep_auto) 
    (* Unfortunately, we have to split on destrmi'-cases manually, else sep-aut introduces schematic before case-split is done *)
    apply (clarsimp simp: mi.case_ifexi_def split: Option.bind_splits IFEXD.splits)
      apply (sep_auto simp: mi.case_ifexi_def)
     apply (sep_auto simp: mi.case_ifexi_def)
    apply (sep_auto simp: mi.case_ifexi_def)
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
declare iteci.simps[code]

lemma iteci_rule: "
  ( mi.ite_impl i t e bdd = Some (p,bdd'))  \<longrightarrow>
  <is_bdd_impl bdd bddi>
    iteci i t e bddi
  <\<lambda>(pi,bddi'). is_bdd_impl bdd' bddi' * \<up>(pi=p )>\<^sub>t"
  apply (induction arbitrary: i t e bddi bdd p bdd' rule: mi.ite_impl.fixp_induct)
    subgoal
      apply simp  (* Warning: Dragons ahead! *)
      using option_admissible[where P=
             "\<lambda>(((x1,x2),x3),x4) (r1,r2). \<forall>bddi. 
              <is_bdd_impl x4 bddi> 
                iteci x1 x2 x3 bddi  
              <\<lambda>r. case r of (pi, bddi') \<Rightarrow> is_bdd_impl r2 bddi' * \<up> (pi = r1)>\<^sub>t"]
      apply auto[1]
      apply (fo_rule subst[rotated])
       apply (assumption)
      by auto
    subgoal by simp
    subgoal
      apply clarify
      apply (clarsimp split: option.splits Option.bind_splits prod.splits)
       apply (subst iteci.simps)
       apply (sep_auto)
      apply (subst iteci.simps)
      apply (sep_auto)
       unfolding imp_to_meta apply rprems
       apply simp
      apply sep_auto
       apply (rule fi_rule)
        apply rprems
        apply simp
       apply frame_inference
      by sep_auto
  done

declare iteci_rule[THEN mp, sep_heap_rules]

definition param_optci where
  "param_optci i t e bdd = do {
    (tr, bdd) \<leftarrow> tci bdd;
    (fl, bdd) \<leftarrow> fci bdd;
    id \<leftarrow> destrci i bdd;
    td \<leftarrow> destrci t bdd;
    ed \<leftarrow> destrci e bdd;
              return (
              if id = TD then Some t else
                        if id = FD then Some e else
                        if td = TD \<and> ed = FD then Some i else
                        if t = e then Some t else
                        if ed = TD \<and> i = t then Some tr else
                        if td = FD \<and> i = e then Some fl else
                        None, bdd)
  }"

lemma param_optci_rule: "
  ( mi.param_opt_impl i t e bdd = Some (p,bdd'))  \<Longrightarrow>
  <is_bdd_impl bdd bddi> 
    param_optci i t e bddi 
  <\<lambda>(pi,bddi'). is_bdd_impl bdd' bddi' * \<up>(pi=p)>\<^sub>t"
by (sep_auto simp add: mi.param_opt_impl.simps param_optci_def tmi'_def fmi'_def
             split: Option.bind_splits)

lemma bdd_hm_lookup_rule: "
  (dcl bdd (i,t,e) = p) \<Longrightarrow>
  <is_bdd_impl bdd bddi> 
    hm_lookup (i, t, e) (dcli bddi)
  <\<lambda>(pi). is_bdd_impl bdd bddi * \<up>(pi = p)>\<^sub>t"
unfolding is_bdd_impl_def by (sep_auto)

lemma bdd_hm_update_rule'[sep_heap_rules]:
  "<is_bdd_impl bdd bddi> 
    hm_update k v (dcli bddi)
  <\<lambda>r. is_bdd_impl (updS bdd k v) (dcli_update (const r) bddi) * true>"
unfolding is_bdd_impl_def updS_def by (sep_auto)

partial_function(heap) iteci_lu where
"iteci_lu i t e s = do {
  lu \<leftarrow> ht_lookup (i,t,e) (dcli s);
  (case lu of Some b \<Rightarrow> return (b,s)
    | None \<Rightarrow> do {
      (po,s) \<leftarrow> param_optci i t e s;
      (case po of Some b \<Rightarrow> do {
        return (b,s)}
      | None \<Rightarrow> do {
        (lt) \<leftarrow> lowest_topsci [i, t, e] s;
        (case lt of Some a \<Rightarrow> do {
        ti \<leftarrow> restrict_topci i a True s;
        tt \<leftarrow> restrict_topci t a True s;
        te \<leftarrow> restrict_topci e a True s;
        fi \<leftarrow> restrict_topci i a False s;
        ft \<leftarrow> restrict_topci t a False s;
        fe \<leftarrow> restrict_topci e a False s;
        (tb,s) \<leftarrow> iteci_lu ti tt te s;
        (fb,s) \<leftarrow> iteci_lu fi ft fe s;
        (r,s) \<leftarrow> ifci a tb fb s;
        cl \<leftarrow> hm_update (i,t,e) r (dcli s);
        return (r,dcli_update (const cl) s)
       } 
         | None \<Rightarrow> raise ''Cannot happen'' )})
  })}"
  
term ht_lookup
declare iteci_lu.simps[code]
thm iteci_lu.simps[unfolded restrict_topci_def case_ifexici_def  param_optci_def lowest_topsci.simps]
partial_function(heap) iteci_lu_code where "iteci_lu_code i t e s = do {
  lu \<leftarrow> hm_lookup (i, t, e) (dcli s);
  case lu of None \<Rightarrow> let po = if i = 1 then Some t
                              else if i = 0 then Some e else if t = 1 \<and> e = 0 then Some i else if t = e then Some t else if e = 1 \<and> i = t then Some 1 else if t = 0 \<and> i = e then Some 0 else None
                     in case po of None \<Rightarrow> do {
                                       id \<leftarrow> destrci i s;
                                       td \<leftarrow> destrci t s;
                                       ed \<leftarrow> destrci e s;
                                       let a = (case id of IFD v t e \<Rightarrow> v);
                                       let a = (case td of IFD v t e \<Rightarrow> min a v | _ \<Rightarrow> a);
                                       let a = (case ed of IFD v t e \<Rightarrow> min a v | _ \<Rightarrow> a);
                                       let ti = (case id of IFD v ti ei \<Rightarrow> if v = a then ti else i | _ \<Rightarrow> i);
                                       let tt = (case td of IFD v ti ei \<Rightarrow> if v = a then ti else t | _ \<Rightarrow> t);
                                       let te = (case ed of IFD v ti ei \<Rightarrow> if v = a then ti else e | _ \<Rightarrow> e);
                                       let fi = (case id of IFD v ti ei \<Rightarrow> if v = a then ei else i | _ \<Rightarrow> i);
                                       let ft = (case td of IFD v ti ei \<Rightarrow> if v = a then ei else t | _ \<Rightarrow> t);
                                       let fe = (case ed of IFD v ti ei \<Rightarrow> if v = a then ei else e | _ \<Rightarrow> e);
                                       (tb, s) \<leftarrow> iteci_lu_code ti tt te s;
                                       (fb, s) \<leftarrow> iteci_lu_code fi ft fe s;
                                       (r, s) \<leftarrow> ifci a tb fb s;
                                       cl \<leftarrow> hm_update (i, t, e) r (dcli s);
                                       return (r, dcli_update (const cl) s)
                                     }
                        | Some b \<Rightarrow> return (b, s)
  | Some b \<Rightarrow> return (b, s)
}"

(* reduced the run-time of our examples by around 30%.
  But we would need some efficient automated machinery to show this,
  and I'm not even sure how to correctly use induction correctly for this.
  Thus: Future work.*)
lemma iteci_lu_code[code_unfold]: "iteci_lu i t e s = iteci_lu_code i t e s"
oops

(* Proof by copy-paste *)
lemma iteci_lu_rule: "
  ( mi.ite_impl_lu i t e bdd = Some (p,bdd'))  \<longrightarrow>
  <is_bdd_impl bdd bddi> 
    iteci_lu i t e bddi 
  <\<lambda>(pi,bddi'). is_bdd_impl bdd' bddi' * \<up>(pi=p )>\<^sub>t"
  apply (induction arbitrary: i t e bddi bdd p bdd' rule: mi.ite_impl_lu.fixp_induct)
    subgoal
      apply simp  (* More Dragons *)
      using option_admissible[where P=
             "\<lambda>(((x1,x2),x3),x4) (r1,r2). \<forall>bddi.
              <is_bdd_impl x4 bddi>
                iteci_lu x1 x2 x3 bddi  
              <\<lambda>r. case r of (pi, bddi') \<Rightarrow> is_bdd_impl r2 bddi' * \<up> (pi = r1)>\<^sub>t"]
      apply auto[1]
      apply (fo_rule subst[rotated])
       apply (assumption)
      (* apply(thin_tac _) That fact is not used\<dots> *)
      by auto
    subgoal by simp
    subgoal
      apply clarify
      apply (clarsimp split: option.splits Option.bind_splits prod.splits)
      subgoal
        unfolding updS_def
        apply (subst iteci_lu.simps)
        apply (sep_auto)
         using bdd_hm_lookup_rule apply(blast)
        apply(sep_auto)
         apply(rule fi_rule)
          apply(rule param_optci_rule)
          apply(sep_auto)
         apply(sep_auto)
        apply(sep_auto)
         unfolding imp_to_meta
         apply(rule fi_rule)
          apply(rprems)
          apply(simp; fail)
         apply(sep_auto)
        apply(sep_auto)
         apply(rule fi_rule)
          apply(rprems)
          apply(simp; fail)
         apply(sep_auto)
         apply(sep_auto)
        unfolding updS_def by (sep_auto)
      subgoal
        apply(subst iteci_lu.simps)
        apply(sep_auto)
         using bdd_hm_lookup_rule apply(blast)
        apply(sep_auto)
         apply(rule fi_rule)
          apply(rule param_optci_rule)
          apply(sep_auto)
         apply(sep_auto)
        by (sep_auto)
      subgoal
        apply(subst iteci_lu.simps)
        apply(sep_auto)
         using bdd_hm_lookup_rule apply(blast)
        by(sep_auto)
      done
  done

declare iteci_lu_rule[THEN mp, sep_heap_rules]

partial_function(heap) sat_listci where
"sat_listci ex s = do {
  d \<leftarrow> destrci ex s;
  case d of 
    FD \<Rightarrow> return None |
    TD \<Rightarrow> return (Some []) |
    IFD v t e \<Rightarrow> do {
      rece \<leftarrow> sat_listci e s;
      case rece of
        Some a \<Rightarrow> return (Some ((v,False)#a)) |
        None \<Rightarrow> do {
          rect \<leftarrow> sat_listci t s;
          return (case rect of
            Some a \<Rightarrow> Some ((v,True)#a) |
            None \<Rightarrow> None)
        }
      }
}"
declare sat_listci.simps[code]

lemma sat_listci_rule: "
  mi.sat_list_impl ex bdd = Some r \<longrightarrow>
  <is_bdd_impl bdd bddi> 
    sat_listci ex bddi 
  <\<lambda>r'. is_bdd_impl bdd bddi * \<up>(r' = r)>"
apply(induction arbitrary: ex bddi bdd r rule: mi.sat_list_impl.fixp_induct)
subgoal
  using option_admissible
    [where P="\<lambda>(x,xb) (xc). \<forall>xa. 
      <is_bdd_impl xb xa> 
       sat_listci x xa 
      <\<lambda>r'. is_bdd_impl xb xa * \<up> (r' = xc)>"] (* Dragons even worse this time. *)
  apply(auto)
  apply(fo_rule subst[rotated])
   apply(assumption)
  by auto

subgoal
  by clarify

subgoal
  apply(unfold imp_to_meta)
  apply(subst sat_listci.simps)
  apply(split Option.bind_splits IFEXD.splits | clarify)+ (* Split on "destrmi' ex bdd = Some _" *)
    apply(sep_auto;fail)
   apply(sep_auto;fail)
  apply(split Option.bind_splits IFEXD.splits option.splits | clarify)+
   apply(rule bind_rule)
    apply(sep_auto;fail)
   apply(clarsimp)
   apply(rule bind_rule)
    apply(rprems)
    apply(assumption)
   apply(sep_auto;fail)
  apply(split Option.bind_splits IFEXD.splits option.splits | clarify)+
    by(sep_auto)+
done
declare sat_listci_rule[unfolded imp_to_meta, sep_heap_rules]

fun sat_list_to_bddci where
"sat_list_to_bddci [] s = tci s" |
"sat_list_to_bddci ((v,u)#us) s = do {
  (r,s) \<leftarrow> sat_list_to_bddci us s;
  (f,s) \<leftarrow> fci s;
  (if u then ifci v r f s else ifci v f r s)
}
"

lemma sat_list_to_bddci_rule[sep_heap_rules]: "
  mi.sat_list_to_bdd sl bdd = Some (r,bdd') \<Longrightarrow>
  <is_bdd_impl bdd bddi> 
    sat_list_to_bddci sl bddi 
  <\<lambda>(r',bddi'). is_bdd_impl bdd' bddi' * \<up>(r' = r)>\<^sub>t"
by(induction arbitrary: bddi bdd bdd' r rule: mi.sat_list_to_bdd.induct;
   sep_auto simp: imp_to_meta split: Option.bind_splits prod.splits)

partial_function(heap) sat_list_coverci where
"sat_list_coverci e s = do {
  sl1 \<leftarrow> sat_listci e s;
  (case sl1 of
      None \<Rightarrow> return ([],s) |
      Some l \<Rightarrow> do {
        (le,s) \<leftarrow> sat_list_to_bddci l s;
        (f,s) \<leftarrow> fci s;
        (lm,s) \<leftarrow> iteci_lu le f e s;
        (rec,s) \<leftarrow> sat_list_coverci lm s;
        return ((l # rec),s)
      }
  )
}"
declare sat_list_coverci.simps[code]


lemma add_true_asm:
  assumes "<b * true> p <a>\<^sub>t"
  shows "<b> p <a>\<^sub>t"
  apply(rule cons_pre_rule)
   prefer 2
   apply(rule assms)
  apply(simp add: ent_true_drop)
  done

lemma add_anything:
  assumes "<b> p <a>"
  shows "<b * x> p <\<lambda>r. a r * x>\<^sub>t"
proof -
  note [sep_heap_rules] = assms
  show ?thesis by sep_auto
qed

lemma add_true:
  assumes "<b> p <a>\<^sub>t"
  shows "<b * true> p <a>\<^sub>t"
  using assms add_anything[where x=true] by force

lemma sat_list_coverci_rule[sep_heap_rules]: "
  mi.sat_list_cover_impl ex bdd = Some (r,bdd') \<longrightarrow>
  <is_bdd_impl bdd bddi> 
    sat_list_coverci ex bddi 
  <\<lambda>(r',bddi'). is_bdd_impl bdd' bddi' * \<up>(r' = r)>\<^sub>t"
apply(induction arbitrary: r ex bddi bdd bdd' r rule: mi.sat_list_cover_impl.fixp_induct)
subgoal
  using option_admissible
    [where P="\<lambda>(xa,xaaa) (x,xaaaa). \<forall>xaa.
      <is_bdd_impl xaaa
       xaa> sat_list_coverci xa xaa
      <\<lambda>r. case r of (r', bddi') \<Rightarrow> is_bdd_impl xaaaa bddi' * \<up> (r' = x)>\<^sub>t"]
  apply(auto)
  apply(fo_rule subst[rotated])
   apply(assumption)
  by auto
subgoal by clarify
subgoal
  apply(subst sat_list_coverci.simps)
  apply(unfold imp_to_meta)
  apply(split Option.bind_splits option.splits | clarify)+
   apply(sep_auto;fail)
  apply(split Option.bind_splits option.splits | clarify)+
   apply(sep_auto)
   apply(rule add_true)
   apply(rprems)
   apply(assumption)
  by(sep_auto)
done

subsection\<open>A standard library of functions\<close>

definition "notci e s \<equiv> do {
  (f,s) \<leftarrow> fci s;
  (t,s) \<leftarrow> tci s;
  iteci_lu e f t s
}"
definition "orci e1 e2 s \<equiv> do {
  (t,s) \<leftarrow> tci s;
  iteci_lu e1 t e2 s
}"
definition "andci e1 e2 s \<equiv> do {
  (f,s) \<leftarrow> fci s;
  iteci_lu e1 e2 f s
}"
definition "norci e1 e2 s \<equiv> do {
  (r,s) \<leftarrow> orci e1 e2 s;
  notci r s
}"
definition "nandci e1 e2 s \<equiv> do {
  (r,s) \<leftarrow> andci e1 e2 s;
  notci r s
}"
definition "biimpci a b s \<equiv> do {
  (nb,s) \<leftarrow> notci b s;
  iteci_lu a b nb s
}"
definition "xorci a b s \<equiv> do {
  (nb,s) \<leftarrow> notci b s;
  iteci_lu a nb b s
}"
definition "litci v bdd \<equiv> do {
  (t,bdd) \<leftarrow> tci bdd;
  (f,bdd) \<leftarrow> fci bdd;
  ifci v t f bdd
}"
definition "tautci v bdd \<equiv> do {
  d \<leftarrow> destrci v bdd;
  return (d = TD)
}"

subsection\<open>Printing\<close>
text\<open>The following functions are exported unverified. They are intended for BDD debugging purposes.\<close>

partial_function(heap) serializeci :: "nat \<Rightarrow> bddi \<Rightarrow> ((nat \<times> nat) \<times> nat) list Heap" where
"serializeci p s = do {
  d \<leftarrow> destrci p s;
  (case d of 
    IFD v t e \<Rightarrow> do {
      r \<leftarrow> serializeci t s;
      l \<leftarrow> serializeci e s;
      return (remdups ([((p,t),1),((p,e),0)] @ r @ l))
    } |
    _ \<Rightarrow> return []
  )
}"
declare serializeci.simps[code]
(* This snaps to heap as a Monad, which is not intended, but irrelevant. *)
fun mapM where
"mapM f [] = return []" |
"mapM f (a#as) = do {
  r \<leftarrow> f a;
  rs \<leftarrow> mapM f as;
  return (r#rs)
}"
definition "liftM f ma = do { a \<leftarrow> ma; return (f a) }"
definition "sequence = mapM id"
term "liftM (map f)"
lemma "liftM (map f) (sequence l) = sequence (map (liftM f) l)"
  apply(induction l)
   apply(simp add: sequence_def liftM_def)
  apply(simp)
oops

(*http://stackoverflow.com/questions/23864965/string-of-nat-in-isabelle*)
fun string_of_nat :: "nat \<Rightarrow> string" where
  "string_of_nat n = (if n < 10 then [char_of_nat (48 + n)]
                                else string_of_nat (n div 10) @ [char_of_nat (48 + (n mod 10))])"

definition labelci :: "bddi \<Rightarrow> nat \<Rightarrow> (string \<times> string \<times> string) Heap" where
"labelci s n = do {
   d \<leftarrow> destrci n s;
   let son = string_of_nat n;
   let label = (case d of
     TD \<Rightarrow> ''T'' |
     FD \<Rightarrow> ''F'' |
     (IFD v _ _) \<Rightarrow> string_of_nat v);
   return (label, son, son @ ''[label='' @ label @ ''];\010'')
}"

definition "graphifyci1 bdd a \<equiv> do {
  let ((f,t),y) = a;
  let c = (string_of_nat f @ '' -> '' @ string_of_nat t);
  return (c @ (case y of 0 \<Rightarrow> '' [style=dotted]'' | Suc _ \<Rightarrow> '''') @ '';\010'')
}"

definition "trd = snd \<circ> snd"
definition "fstp = apsnd fst"

definition "the_thing_By f l = (let 
  nub = remdups (map fst l) in
  map (\<lambda>e. (e, map snd (filter (\<lambda>g. (f e (fst g))) l))) nub)"
definition "the_thing = the_thing_By (op =)"


definition graphifyci :: "string \<Rightarrow> nat \<Rightarrow> bddi \<Rightarrow> string Heap" where
"graphifyci name ep bdd \<equiv> do {
  s \<leftarrow> serializeci ep bdd;
  let e = map fst s;
  l \<leftarrow> mapM (labelci bdd) (rev (remdups (map fst e @ map snd e)));
  let grp =  (map (\<lambda>l. foldr (\<lambda>a t. t @ a @ '';'') (snd l) ''{rank=same;'' @ ''}\010'') (the_thing (map fstp l)));
  e \<leftarrow> mapM (graphifyci1 bdd) s;
  let emptyhlp = (case ep of 0 \<Rightarrow> ''F;\010'' | Suc 0 \<Rightarrow> ''T;\010'' | _ \<Rightarrow> '''');  
  return (''digraph '' @ name @ '' {\010'' @ concat (map trd l) @ concat grp @ concat e @ emptyhlp @ ''}'')
}"

end

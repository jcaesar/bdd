section\<open>Abstract ITE Implementation\<close>
theory Abstract_Impl
imports BDT
        "$AFP/Automatic_Refinement/Lib/Refine_Lib"
        Option_Helpers
begin

datatype ('a, 'ni) IFEXD = TD | FD | IFD 'a 'ni 'ni 

locale bdd_impl_pre =
  fixes R :: "'s \<Rightarrow> ('ni \<times> ('a :: linorder) ifex) set"
  fixes I :: "'s \<Rightarrow> bool"
begin
  definition les:: "'s \<Rightarrow> 's \<Rightarrow> bool" where
  "les s s' == \<forall>ni n. (ni, n) \<in> R s \<longrightarrow> (ni, n) \<in> R s'"
end

locale bdd_impl = bdd_impl_pre R for R :: "'s \<Rightarrow> ('ni \<times> ('a :: linorder) ifex) set" +
  fixes Timpl :: "'s \<rightharpoonup> ('ni \<times> 's)"
  fixes Fimpl :: "'s \<rightharpoonup> ('ni \<times> 's)"
  fixes IFimpl :: "'a \<Rightarrow> 'ni \<Rightarrow> 'ni \<Rightarrow> 's \<rightharpoonup> ('ni \<times> 's)"
  fixes DESTRimpl :: "'ni  \<Rightarrow> 's \<rightharpoonup> ('a, 'ni) IFEXD"

  assumes Timpl_rule: "I s \<Longrightarrow> ospec (Timpl s) (\<lambda>(ni, s'). (ni, Trueif) \<in> R s' \<and> I s' \<and> les s s')"
  assumes Fimpl_rule: "I s \<Longrightarrow> ospec (Fimpl s) (\<lambda>(ni, s'). (ni, Falseif) \<in> R s' \<and> I s' \<and> les s s')"
  assumes IFimpl_rule: "\<lbrakk>I s; (ni1,n1) \<in> R s;(ni2,n2) \<in> R s\<rbrakk>
                        \<Longrightarrow> ospec (IFimpl v ni1 ni2 s) (\<lambda>(ni, s'). (ni, IFC v n1 n2) \<in> R s' \<and> I s' \<and> les s s')"

  assumes DESTRimpl_rule1: "I s \<Longrightarrow> (ni, Trueif) \<in> R s \<Longrightarrow> ospec (DESTRimpl ni s) (\<lambda>r. r = TD)"
  assumes DESTRimpl_rule2: "I s \<Longrightarrow> (ni, Falseif) \<in> R s \<Longrightarrow> ospec (DESTRimpl ni s) (\<lambda>r. r = FD)"
  assumes DESTRimpl_rule3: "I s \<Longrightarrow> (ni, IF v n1 n2) \<in> R s \<Longrightarrow>
                            ospec (DESTRimpl ni s)
                                  (\<lambda>r. \<exists>ni1 ni2. r = (IFD v ni1 ni2) \<and> (ni1, n1) \<in> R s \<and> (ni2, n2) \<in> R s)"
begin

lemma les_refl[simp,intro!]:"les s s" by (auto simp add: les_def)
lemma les_trans[trans]:"les s1 s2 \<Longrightarrow> les s2 s3 \<Longrightarrow> les s1 s3" by (auto simp add: les_def)
lemmas DESTRimpl_rules = DESTRimpl_rule1 DESTRimpl_rule2 DESTRimpl_rule3

lemma DESTRimpl_rule_useless:
  "I s \<Longrightarrow> (ni, n) \<in> R s \<Longrightarrow> ospec (DESTRimpl ni s) (\<lambda>r. (case r of
    TD \<Rightarrow> (ni, Trueif) \<in> R s |
    FD \<Rightarrow> (ni, Falseif) \<in> R s |
    IFD v nt ne \<Rightarrow> (\<exists>t e. n = IF v t e \<and> (ni, IF v t e) \<in> R s)))"
by(cases n; clarify; drule (1) DESTRimpl_rules; drule ospecD2; clarsimp)
lemma DESTRimpl_rule: 
  "I s \<Longrightarrow> (ni, n) \<in> R s \<Longrightarrow> ospec (DESTRimpl ni s) (\<lambda>r. (case n of
    Trueif \<Rightarrow> r = TD |
    Falseif \<Rightarrow> r = FD |
    IF v t e \<Rightarrow> (\<exists>tn en. r = IFD v tn en \<and> (tn,t) \<in> R s \<and> (en,e) \<in> R s)))"
by(cases n; clarify; drule (1) DESTRimpl_rules; drule ospecD2; clarsimp)

definition "case_ifexi fti ffi fii ni s \<equiv> do {
  dest \<leftarrow> DESTRimpl ni s;
  case dest of
    TD \<Rightarrow> fti s
  | FD \<Rightarrow> ffi s
  | IFD v ti ei \<Rightarrow> fii v ti ei s}"

lemma case_ifexi_rule:
  assumes INV: "I s"
  assumes NI: "(ni,n)\<in>R s"
  assumes FTI: "\<lbrakk> n = Trueif \<rbrakk> \<Longrightarrow> ospec (fti s) (\<lambda>(r,s'). (r,ft) \<in> Q s \<and> I' s')"
  assumes FFI: "\<lbrakk> n = Falseif \<rbrakk> \<Longrightarrow> ospec (ffi s) (\<lambda>(r,s'). (r,ff) \<in> Q s \<and> I' s')"
  assumes FII: "\<And>ti ei v t e. \<lbrakk> n = IF v t e; (ti,t)\<in>R s; (ei,e)\<in>R s \<rbrakk> \<Longrightarrow> ospec (fii v ti ei s) (\<lambda>(r,s'). (r,fi v t e) \<in> Q s \<and> I' s')"
  shows "ospec (case_ifexi fti ffi fii ni s) (\<lambda>(r,s'). (r,case_ifex ft ff fi n) \<in> Q s \<and> I' s')"
  unfolding case_ifexi_def
  apply (cases n)
    subgoal
      apply (rule obind_rule)
       apply (rule DESTRimpl_rule1[OF INV])
       using NI FTI by (auto)
    subgoal
      apply (rule obind_rule)
       apply (rule DESTRimpl_rule2[OF INV])
       using NI FFI by (auto)
    subgoal
      apply (rule obind_rule)
       apply (rule DESTRimpl_rule3[OF INV])
       using NI FII by (auto)
done

abbreviation "return x \<equiv> \<lambda>s. Some (x,s)"

primrec lowest_tops_impl where
"lowest_tops_impl [] s = Some (None,s)" |
"lowest_tops_impl (e#es) s =
    case_ifexi
      (\<lambda>s. lowest_tops_impl es s)
      (\<lambda>s. lowest_tops_impl es s)
      (\<lambda>v t e s. do {
      (rec,s) \<leftarrow> lowest_tops_impl es s;
        (case rec of
          Some u \<Rightarrow> Some ((Some (min u v)), s) | 
          None \<Rightarrow> Some ((Some v), s))
       }) e s"

declare lowest_tops_impl.simps[simp del]

fun lowest_tops_alt where
"lowest_tops_alt [] = None" |
"lowest_tops_alt (e#es) = (
    let rec = lowest_tops_alt es in
    case_ifex
      rec
      rec
      (\<lambda>v t e. (case rec of 
          Some u \<Rightarrow> (Some (min u v)) | 
          None \<Rightarrow> (Some v))
       ) e
  )"

lemma lowest_tops_alt: "lowest_tops l = lowest_tops_alt l" 
  by (induction l rule: lowest_tops.induct) (auto split: option.splits simp: lowest_tops.simps)

lemma lowest_tops_impl_R: 
  assumes "list_all2 (in_rel (R s)) li l" "I s"
  shows "ospec (lowest_tops_impl li s) (\<lambda>(r,s'). r = lowest_tops l \<and> s'=s)"
  unfolding lowest_tops_alt
  using assms apply (induction rule: list_all2_induct)
   subgoal by (simp add: lowest_tops_impl.simps)
   subgoal
     apply (simp add: lowest_tops_impl.simps)
     apply (rule case_ifexi_rule[where Q="\<lambda>s. Id", unfolded pair_in_Id_conv])
      apply assumption+
     apply (rule obind_rule)
      apply assumption
     apply (clarsimp split: option.splits)
    done
  done


definition restrict_top_impl where
"restrict_top_impl e vr vl s = 
  case_ifexi
    (return e)
    (return e)
    (\<lambda>v te ee. return (if v = vr then (if vl then te else ee) else e))
    e s
  "

lemma restrict_top_alt: "restrict_top n var val = (case n of 
  (IF v t e) \<Rightarrow> (if v = var then (if val then t else e) else (IF v t e))
| _ \<Rightarrow> n)"
  apply (induction n var val rule: restrict_top.induct)
  apply (simp_all)
  done

lemma restrict_top_impl_spec: "I s \<Longrightarrow> (ni,n) \<in> R s \<Longrightarrow> ospec (restrict_top_impl ni vr vl s) (\<lambda>(res,s'). (res, restrict_top n vr vl) \<in> R s \<and> s'=s)"
  unfolding restrict_top_impl_def restrict_top_alt
  by (rule case_ifexi_rule[where I'="\<lambda>s'. s'=s" and Q="R", simplified]) auto


partial_function(option) ite_impl where
"ite_impl i t e s = do {
  (lt,_) \<leftarrow> lowest_tops_impl [i, t, e] s;
  (case lt of
    Some a \<Rightarrow> do {
      (ti,_) \<leftarrow> restrict_top_impl i a True s;
      (tt,_) \<leftarrow> restrict_top_impl t a True s;
      (te,_) \<leftarrow> restrict_top_impl e a True s;
      (fi,_) \<leftarrow> restrict_top_impl i a False s;
      (ft,_) \<leftarrow> restrict_top_impl t a False s;
      (fe,_) \<leftarrow> restrict_top_impl e a False s;
      (tb,s) \<leftarrow> ite_impl ti tt te s;
      (fb,s) \<leftarrow> ite_impl fi ft fe s;
      IFimpl a tb fb s}
  | None \<Rightarrow> case_ifexi (\<lambda>_.(Some (t,s))) (\<lambda>_.(Some (e,s))) (\<lambda>_ _ _ _. None) i s 
)}"

lemma ite_impl_R: "I s
       \<Longrightarrow> in_rel (R s) ii i \<Longrightarrow> in_rel (R s) ti t \<Longrightarrow> in_rel (R s) ei e
       \<Longrightarrow> ospec (ite_impl ii ti ei s) (\<lambda>(r, s'). (r, ifex_ite i t e) \<in> R s' \<and> I s' \<and> les s s')"
proof(induction i t e arbitrary: s ii ti ei rule: ifex_ite.induct, goal_cases)
  case (1 i t e s ii ti ei) note goal1 = 1
  have la2: "list_all2 (in_rel (R s)) [ii,ti,ei] [i,t,e]" using goal1(4-6) by simp
  show ?case proof(cases "lowest_tops [i,t,e]")
    case None from goal1(3-6) show ?thesis
        apply(subst ite_impl.simps)
        apply(rule obind_rule[where Q="\<lambda>(r, s'). r = lowest_tops [i,t,e] \<and> s'=s"])
         apply(rule ospec_cons)
          apply(rule lowest_tops_impl_R[OF la2])
          apply(assumption)
         apply(clarsimp split: prod.splits)
        apply(simp add: None split: prod.splits)
        apply(clarsimp)
        apply(rule ospec_cons)
         apply(rule case_ifexi_rule[where I'="\<lambda>s'. s'=s"])
        using None by (auto split: prod.splits ifex.splits simp: lowest_tops.simps)
    next
    case (Some lv)
      note mIH = goal1(1,2)[OF Some]
      from goal1(3-6) show ?thesis
        apply(subst ite_impl.simps)
        apply(rule obind_rule[where Q="\<lambda>(r, s'). r = lowest_tops [i,t,e]"])
         apply(rule ospec_cons)
          apply(rule lowest_tops_impl_R[OF la2])
          apply(assumption)
         apply(clarsimp split: prod.splits)
        apply(simp add: Some split: prod.splits)
        apply(clarsimp)
        (* take care of all those restrict_tops *)
        apply(rule obind_rule, rule restrict_top_impl_spec, assumption+, clarsimp split: prod.splits)+
        apply(rule obind_rule)
         apply(rule mIH(1))
            apply(simp;fail)+
        apply(clarsimp)
        apply(rule obind_rule)
         apply(rule mIH(2))
            apply(simp add: les_def;fail)+
        apply(simp split: prod.splits)
        apply(rule ospec_cons)
         apply(rule IFimpl_rule)
           apply(simp add: les_def;fail)+
           using les_def les_trans by blast+
    qed
qed

lemma case_ifexi_mono[partial_function_mono]:
  assumes [partial_function_mono]: 
    "mono_option (\<lambda>F. fti F s)"
    "mono_option (\<lambda>F. ffi F s)"
    "\<And>x31 x32 x33. mono_option (\<lambda>F. fii F x31 x32 x33 s)"
  shows "mono_option (\<lambda>F. case_ifexi (fti F) (ffi F) (fii F) ni s)"
  unfolding case_ifexi_def by (tactic \<open>Partial_Function.mono_tac @{context} 1\<close>)

partial_function(option) val_impl :: "'ni \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> (bool\<times>'s) option"
where
"val_impl e ass s = case_ifexi
  (\<lambda>s. Some (True,s))
  (\<lambda>s. Some (False,s)) 
  (\<lambda>v t e s. val_impl (if ass v then t else e) ass s)
  e  s"

lemma "I s \<Longrightarrow> (ni,n) \<in> R s \<Longrightarrow> ospec (val_impl ni ass s) (\<lambda>(r,s'). r = (val_ifex n ass) \<and> s'=s)"
  apply (induction n arbitrary: ni)
  subgoal
   apply (subst val_impl.simps)
   apply (rule ospec_cons)
    apply (rule case_ifexi_rule[where I'="\<lambda>s'. s'=s" and Q="\<lambda>s. Id"]; assumption?)
      by auto
  subgoal
   apply (subst val_impl.simps)
   apply (rule ospec_cons)
    apply (rule case_ifexi_rule[where I'="\<lambda>s'. s'=s" and Q="\<lambda>s. Id"]; assumption?)
      by auto
  subgoal
   apply (subst val_impl.simps)
   apply (subst val_ifex.simps)
   apply (clarsimp; intro impI conjI)
    apply (rule ospec_cons)
     apply (rule case_ifexi_rule[where I'="\<lambda>s'. s'=s" and Q="\<lambda>s. Id"]; assumption?)
       apply (simp; fail)
      apply (simp; fail)
     apply (rule ospec_cons)
      apply (rprems; simp; fail)
     apply (simp; fail)
    apply (simp; fail)
   apply (rule ospec_cons)
    apply (rule case_ifexi_rule[where I'="\<lambda>s'. s'=s" and Q="\<lambda>s. Id"]; assumption?)
      apply (simp; fail)
     apply (simp; fail)
    apply(simp)
    apply (rule ospec_cons)
     apply (rprems; simp; fail)
    apply (simp; fail)
   apply (simp; fail)
   done
  done

end

locale bdd_impl_cmp_pre = bdd_impl_pre
begin

definition "map_invar_impl m s = 
  (\<forall>ii ti ei ri. m (ii,ti,ei) = Some ri \<longrightarrow> 
  (\<exists>i t e. ((ri,ifex_ite_opt i t e) \<in> R s) \<and> (ii,i) \<in> R s \<and> (ti,t) \<in> R s \<and> (ei,e) \<in> R s))"

lemma map_invar_impl_les: "map_invar_impl m s \<Longrightarrow> les s s' \<Longrightarrow> map_invar_impl m s'"
  unfolding map_invar_impl_def bdd_impl_pre.les_def by blast

lemma map_invar_impl_update: "map_invar_impl m s \<Longrightarrow> 
       (ii,i) \<in> R s \<Longrightarrow> (ti,t) \<in> R s \<Longrightarrow> (ei,e) \<in> R s \<Longrightarrow>
       (ri, ifex_ite_opt i t e) \<in> R s \<Longrightarrow> map_invar_impl (m((ii,ti,ei) \<mapsto> ri)) s"
unfolding map_invar_impl_def by auto

end

locale bdd_impl_cmp = bdd_impl + bdd_impl_cmp_pre +
  fixes M :: "'a \<Rightarrow> ('b \<times> 'b \<times> 'b) \<Rightarrow> 'b option"
  fixes U :: "'a \<Rightarrow> ('b \<times> 'b \<times> 'b) \<Rightarrow> 'b \<Rightarrow> 'a"
  fixes cmp :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  assumes cmp_rule1: "I s \<Longrightarrow> (ni, i) \<in> R s \<Longrightarrow> (ni', i) \<in> R s \<Longrightarrow> cmp ni ni'"
  assumes cmp_rule2: "I s \<Longrightarrow> cmp ni ni' \<Longrightarrow> (ni, i) \<in> R s \<Longrightarrow> (ni', i') \<in> R s \<Longrightarrow> i = i'"
  assumes map_invar_rule1: "I s \<Longrightarrow> map_invar_impl (M s) s"
  assumes map_invar_rule2: "I s \<Longrightarrow> (ii,it) \<in> R s \<Longrightarrow> (ti,tt) \<in> R s \<Longrightarrow> (ei,et) \<in> R s \<Longrightarrow>
                            (ri, ifex_ite_opt it tt et) \<in> R s \<Longrightarrow> U s (ii,ti,ei) ri = s' \<Longrightarrow>
                            I s'"
  assumes map_invar_rule3: "I s \<Longrightarrow> R (U s (ii, ti, ei) ri) = R s"
begin

lemma cmp_rule_eq: "I s \<Longrightarrow>  (ni, i) \<in> R s \<Longrightarrow> (ni', i') \<in> R s \<Longrightarrow> cmp ni ni' \<longleftrightarrow> i = i'"
  using cmp_rule1 cmp_rule2 by force

lemma DESTRimpl_Some: "I s \<Longrightarrow> (ni, i) \<in> R s \<Longrightarrow> ospec (DESTRimpl ni s) (\<lambda>r. True)"
  apply(cases i)
    apply(auto intro: ospec_cons dest: DESTRimpl_rules)
done

fun param_opt_impl where
  "param_opt_impl i t e s =  do {
    ii \<leftarrow> DESTRimpl i s;
    ti \<leftarrow> DESTRimpl t s;
    ei \<leftarrow> DESTRimpl e s;
    (tn,s) \<leftarrow> Timpl s;
    (fn,s) \<leftarrow> Fimpl s;
    Some ((if ii = TD then Some t else
    if ii = FD then Some e else
    if ti = TD \<and> ei = FD then Some i else
    if cmp t e then Some t else
    if ei = TD \<and> cmp i t then Some tn else
    if ti = FD \<and> cmp i e then Some fn else
    None), s)}"

declare param_opt_impl.simps[simp del]

lemma param_opt_impl_lesI: 
  assumes "I s" "(ii,i) \<in> R s" "(ti,t) \<in> R s" "(ei,e) \<in> R s"
  shows "ospec (param_opt_impl ii ti ei s) 
               (\<lambda>(r,s'). I s' \<and> les s s')"
  using assms apply(subst param_opt_impl.simps)
  by (auto simp add: param_opt_def les_def intro!: obind_rule
                dest: DESTRimpl_Some Timpl_rule Fimpl_rule)

lemma param_opt_impl_R: 
  assumes "I s" "(ii,i) \<in> R s" "(ti,t) \<in> R s" "(ei,e) \<in> R s"
  shows "ospec (param_opt_impl ii ti ei s)
               (\<lambda>(r,s'). case r of None \<Rightarrow> param_opt i t e = None
                                 | Some r \<Rightarrow> (\<exists>r'. param_opt i t e  = Some r' \<and> (r, r') \<in> R s'))"
  using assms apply(subst param_opt_impl.simps)
  apply(rule obind_rule)
   apply(rule DESTRimpl_rule; assumption)
  apply(rule obind_rule)
   apply(rule DESTRimpl_rule; assumption)
  apply(rule obind_rule)
   apply(rule DESTRimpl_rule; assumption)
  apply(rule obind_rule)
   apply(rule Timpl_rule; assumption)
  apply(safe)
  apply(rule obind_rule)
   apply(rule Fimpl_rule; assumption)
  by (auto simp add: param_opt_def les_def cmp_rule_eq split: ifex.splits)

partial_function(option) ite_impl_opt where
"ite_impl_opt i t e s = do {
  (ld, s) \<leftarrow>  param_opt_impl i t e s;
  (case ld of Some b \<Rightarrow> Some (b, s) |
  None \<Rightarrow>
  do {
  (lt,_) \<leftarrow> lowest_tops_impl [i, t, e] s;
  (case lt of
    Some a \<Rightarrow> do {
      (ti,_) \<leftarrow> restrict_top_impl i a True s;
      (tt,_) \<leftarrow> restrict_top_impl t a True s;
      (te,_) \<leftarrow> restrict_top_impl e a True s;
      (fi,_) \<leftarrow> restrict_top_impl i a False s;
      (ft,_) \<leftarrow> restrict_top_impl t a False s;
      (fe,_) \<leftarrow> restrict_top_impl e a False s;
      (tb,s) \<leftarrow> ite_impl_opt ti tt te s;
      (fb,s) \<leftarrow> ite_impl_opt fi ft fe s;
      IFimpl a tb fb s}
  | None \<Rightarrow> case_ifexi (\<lambda>_.(Some (t,s))) (\<lambda>_.(Some (e,s))) (\<lambda>_ _ _ _. None) i s 
)})}"

lemma ospec_and: "ospec f P \<Longrightarrow> ospec f Q \<Longrightarrow> ospec f (\<lambda>x. P x \<and> Q x)"
  using ospecD2 by force

lemma ite_impl_opt_R: "
  I s
  \<Longrightarrow> in_rel (R s) ii i \<Longrightarrow> in_rel (R s) ti t \<Longrightarrow> in_rel (R s) ei e
  \<Longrightarrow> ospec (ite_impl_opt ii ti ei s) (\<lambda>(r, s'). (r, ifex_ite_opt i t e) \<in> R s' \<and> I s' \<and> les s s')"
proof(induction i t e arbitrary: s ii ti ei rule: ifex_ite_opt.induct, goal_cases)
  note ifex_ite_opt.simps[simp del] restrict_top.simps[simp del]
  case (1 i t e s ii ti ei) note goal1 = 1
  have la2: "list_all2 (in_rel (R s)) [ii,ti,ei] [i,t,e]" using goal1(4-6) by simp
  note mIH = goal1(1,2)
  from goal1(3-6) show ?case
    apply(cases "param_opt i t e")
     defer
     apply(subst ite_impl_opt.simps)
      apply(rule obind_rule)
       apply(rule ospec_and[OF param_opt_impl_R param_opt_impl_lesI])
             apply(auto simp add: les_def ifex_ite_opt.simps split: option.splits)[9]
    (* param_opt i t e = None *)
    apply(frule param_opt_lowest_tops_lem)
    apply(clarsimp)
    apply(subst ite_impl_opt.simps)
     apply(rule obind_rule)
     apply(rule ospec_and[OF param_opt_impl_R param_opt_impl_lesI])
            apply(auto split: option.splits)[8]
    apply(clarsimp split: option.splits)
    apply(rule obind_rule[where Q="\<lambda>(r, s'). r = lowest_tops [i,t,e]"])
     apply(rule ospec_cons)
      apply(rule lowest_tops_impl_R)
       using les_def apply(fastforce)
      apply(assumption)
     apply(fastforce)
    using BDT.param_opt_lowest_tops_lem apply(clarsimp split: prod.splits)
    (* take care of all those restrict_tops *)
    apply(rule obind_rule, rule restrict_top_impl_spec, assumption, auto simp add: les_def split: prod.splits)+
    apply(rule obind_rule)
     apply(rule mIH(1))
          apply(simp add: les_def;fail)+
    apply(clarsimp)
     apply(rule obind_rule)
     apply(rule mIH(2))
          apply(simp add: les_def;fail)+
    apply(simp add: ifex_ite_opt.simps split: prod.splits)
    apply(rule ospec_cons)
     apply(rule IFimpl_rule)
       apply(auto simp add: les_def;fail)+
    done
qed

partial_function(option) ite_impl_lu where
"ite_impl_lu i t e s = do {
  (case M s (i,t,e) of Some b \<Rightarrow> Some (b,s) | None \<Rightarrow> do {
  (ld, s) \<leftarrow>  param_opt_impl i t e s;
  (case ld of Some b \<Rightarrow> Some (b, s) |
  None \<Rightarrow>
  do {
  (lt,_) \<leftarrow> lowest_tops_impl [i, t, e] s;
  (case lt of
    Some a \<Rightarrow> do {
      (ti,_) \<leftarrow> restrict_top_impl i a True s;
      (tt,_) \<leftarrow> restrict_top_impl t a True s;
      (te,_) \<leftarrow> restrict_top_impl e a True s;
      (fi,_) \<leftarrow> restrict_top_impl i a False s;
      (ft,_) \<leftarrow> restrict_top_impl t a False s;
      (fe,_) \<leftarrow> restrict_top_impl e a False s;
      (tb,s) \<leftarrow> ite_impl_lu ti tt te s;
      (fb,s) \<leftarrow> ite_impl_lu fi ft fe s;
      (r,s) \<leftarrow> IFimpl a tb fb s;
      let s = U s (i,t,e) r;
      Some (r,s)
      } |
    None \<Rightarrow> None
)})})}"

declare ifex_ite_opt.simps[simp del]

lemma ite_impl_lu_R: "I s
       \<Longrightarrow> (ii,i) \<in> R s \<Longrightarrow> (ti,t) \<in> R s \<Longrightarrow> (ei,e) \<in> R s
       \<Longrightarrow> ospec (ite_impl_lu ii ti ei s) 
                 (\<lambda>(r, s'). (r, ifex_ite_opt i t e) \<in> R s' \<and> I s' \<and> les s s')"
proof(induction i t e arbitrary: s ii ti ei rule: ifex_ite_opt.induct, goal_cases)
  note restrict_top.simps[simp del]
  case (1 i t e s ii ti ei) note goal1 = 1
  have la2: "list_all2 (in_rel (R s)) [ii,ti,ei] [i,t,e]" using goal1(4-6) by simp
  note mIH = goal1(1,2)
  from goal1(3-6) show ?case
    apply(subst ite_impl_lu.simps)
    apply(cases "M s (ii, ti, ei)")
     defer
     (* M s (ii, ti, ei) = Some a *)
     apply(frule map_invar_rule1)
     apply(simp only: option.simps ospec.simps prod.simps simp_thms les_refl)
     apply(subst (asm) map_invar_impl_def)
     apply(erule allE[where x = ii])
     apply(erule allE[where x = ti])
     apply(erule allE[where x = ei])
     apply(rename_tac a)
     apply(erule_tac x = a in allE)
     apply(metis cmp_rule_eq)
    (* M s (ii, ti, ei) = Some a *)
    apply(clarsimp)
    apply(cases "param_opt i t e")
     defer
     (* param_opt i t e = Some a *)
     apply(rule obind_rule)
      apply(rule ospec_and[OF param_opt_impl_R param_opt_impl_lesI])
             apply(auto simp add: map_invar_impl_les ifex_ite_opt.simps  split: option.splits)[9]
    (* param_opt i t e = None *)
    apply(frule param_opt_lowest_tops_lem)
    apply(clarsimp)
    apply(rule obind_rule)
     apply(rule ospec_and[OF param_opt_impl_R param_opt_impl_lesI])
             apply(auto split: option.splits)[8]
    apply(clarsimp split: option.splits)
    apply(rule_tac obind_rule[where Q="\<lambda>(r, s'). r = lowest_tops [i,t,e]"])
     apply(rule ospec_cons)
      apply(rule lowest_tops_impl_R)
       using les_def apply(fastforce)
      apply(assumption)
     apply(fastforce)
    using BDT.param_opt_lowest_tops_lem apply(clarsimp split: prod.splits)
    apply(rule obind_rule, rule restrict_top_impl_spec, assumption+, auto simp add: les_def split: prod.splits)+
    apply(rule obind_rule)
     apply(rule mIH(1))
          apply(simp add: map_invar_impl_les les_def;fail)+
    apply(clarsimp)
    apply(rule obind_rule)
     apply(rule mIH(2))
          apply(simp add: map_invar_impl_les les_def;fail)+
    apply(simp add: ifex_ite_opt.simps split: prod.splits)
    apply(rule obind_rule)
     apply(rule IFimpl_rule)
       apply(simp)
      apply(auto simp add: les_def)[2]
    apply(clarsimp simp add: les_def)
    apply(safe)
    using map_invar_rule3 apply(presburger)
     apply(rule map_invar_rule2)
          prefer 6 apply(blast)
         apply(blast)
        apply(blast)
       apply(blast)
      apply(blast)
     apply(clarsimp simp add: ifex_ite_opt.simps)
    using map_invar_rule3 by presburger
qed


(* I could move this stuff into one of the not-so-strong locales. But for what? *)
partial_function(option) sat_list_impl where
"sat_list_impl ex s = do {
  d \<leftarrow> DESTRimpl ex s;
  case d of 
    FD \<Rightarrow> Some None |
    TD \<Rightarrow> Some (Some []) |
    IFD v t e \<Rightarrow> do {
      rece \<leftarrow> sat_list_impl e s;
      case rece of
        Some a \<Rightarrow> Some (Some ((v,False)#a)) |
        None \<Rightarrow> do {
          rect \<leftarrow> sat_list_impl t s;
          Some (case rect of
            Some a \<Rightarrow> Some ((v,True)#a) |
            None \<Rightarrow> None)
        }
      }
}"

lemma sat_list_impl_spec: "I s \<Longrightarrow> (ni,n) \<in> R s \<Longrightarrow> ospec (sat_list_impl ni s) (\<lambda>rl. rl = ifex_sat_list n)"
  apply(induction n arbitrary: ni rule: ifex_sat_list.induct)
    apply(auto simp add: sat_list_impl.simps intro: obind_rule elim: DESTRimpl_rule1 DESTRimpl_rule2)[2]
  apply(subst sat_list_impl.simps)
  apply(auto intro!: obind_rule elim: DESTRimpl_rule3)
   apply(rprems)
   apply(assumption)
  apply(split option.splits)
  apply(intro conjI[rotated])
   apply(simp;fail)
  apply(clarsimp)
  apply(auto intro!: obind_rule elim: DESTRimpl_rule3)
done

fun sat_list_to_bdd where
"sat_list_to_bdd [] s = Timpl s" |
"sat_list_to_bdd ((v,u)#us) s = do {
  (r,s) \<leftarrow> sat_list_to_bdd us s;
  (f,s) \<leftarrow> Fimpl s;
  (if u then IFimpl v r f s else IFimpl v f r s)
}
"

lemma lesI: "(a,b) \<in> R s \<Longrightarrow> les s s' \<Longrightarrow> (a,b) \<in> R s'" unfolding les_def by simp

lemma sat_list_to_bdd_spec: "I s \<Longrightarrow> ospec (sat_list_to_bdd u s) (\<lambda>(r,s'). I s' \<and> (r, sat_list_to_bdt u) \<in> R s' \<and> les s s')"
  apply(induction arbitrary: s rule: sat_list_to_bdt.induct)
   apply(auto intro: obind_rule elim: Timpl_rule[THEN ospec_cons])[1]
  apply(subst sat_list_to_bdd.simps)
  apply(intro obind_rule)
   apply(subgoal_tac "ospec (sat_list_to_bdd us s) (\<lambda>(r, s'). I s' \<and> (r, sat_list_to_bdt us) \<in> R s' \<and> les s s')") (* the things you do if rprems doesn't work\<dots> *)
    apply(assumption)
   subgoal by auto
  apply(clarify)
  apply(intro obind_rule)
  apply(erule Fimpl_rule)
  apply(clarsimp; intro conjI; clarify)
  (* * *)
   apply(rule ospec_cons)
    apply(erule IFimpl_rule)
     apply(erule (1) lesI)
    apply(erule lesI)
    apply(rule les_refl;fail)
   apply(clarify)
   apply(auto simp add: IFC_def)[1]
   apply((erule les_trans)+, rule les_refl; fail)
  (* it is nearly the same reasoning again as from * *)
  apply(rule ospec_cons)
   apply(erule IFimpl_rule)
    apply(erule lesI; rule les_refl;fail)
   apply(((erule lesI)+, assumption | rule les_refl); fail)
  apply(auto simp add: IFC_def)
  apply((erule les_trans)+, rule les_refl; fail)
done

function sat_list_cover_impls where
"sat_list_cover_impls e = (if ro_ifex e then
	(case ifex_sat_list e of
		None \<Rightarrow> [] | 
		Some l \<Rightarrow> let 
			le = sat_list_to_bdt l;
			lm = ifex_ite le Falseif e in
			l # ifex_sat_list_cover lm)
	else [])"
by clarsimp+

partial_function(option) sat_list_cover_impl where
"sat_list_cover_impl e s = do {
  sl1 \<leftarrow> sat_list_impl e s;
  (case sl1 of
      None \<Rightarrow> Some ([],s) |
      Some l \<Rightarrow> do {
        (le,s) \<leftarrow> sat_list_to_bdd l s;
        (f,s) \<leftarrow> Fimpl s;
        (lm,s) \<leftarrow> ite_impl_lu le f e s;
        (rec,s) \<leftarrow> sat_list_cover_impl lm s;
        Some ((l # rec),s)
      }
  )
}"

lemma restrict_top_impl_spec: "ro_ifex n (* børk *) \<Longrightarrow> I s \<Longrightarrow> (ni,n) \<in> R s \<Longrightarrow> ospec (sat_list_cover_impl ni s) (\<lambda>(rl,s'). rl = ifex_sat_list_cover n \<and> I s' \<and> les s s')"
  apply(induction n arbitrary: ni s rule: ifex_sat_list_cover.induct)
  apply(subst sat_list_cover_impl.simps)
  apply(rule obind_rule)
   apply(erule (1) sat_list_impl_spec)
  apply(split option.splits)
  apply(intro conjI)
   apply(simp;fail)
  apply(clarify, intro obind_rule)
   apply(erule sat_list_to_bdd_spec)
  apply(clarify, intro obind_rule)
   apply(erule Fimpl_rule)
  apply(clarify, intro obind_rule)
   apply(erule ite_impl_lu_R)
   apply(auto elim: lesI les_trans)[3]
  apply(clarify, intro obind_rule)
   apply(rprems)
         apply(clarify;fail)
        apply(assumption)
       apply(rule refl, rule refl)
     apply(meson ifex_minimal.simps(3) ifex_ordered.simps(3) minimal_ifex_ite_invar order_ifex_ite_invar sat_list_to_bdt_minimal sat_list_to_bdt_ordered) (* TODO: make a rule for this *)
    apply(assumption)
   apply(simp add: ifex_ite_opt_eq sat_list_to_bdt_minimal sat_list_to_bdt_ordered) (* and for this? *)
  apply(clarify)
  apply(rule oreturn_rule)
  apply(clarify)
  apply(intro conjI[rotated])
    apply(elim les_trans; rule les_refl; fail)
   apply(assumption)
  apply(simp)
done

end
end

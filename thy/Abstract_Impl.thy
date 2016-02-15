section{*Abstract ITE Implementation*}
theory Abstract_Impl
imports BDT
        "$AFP/Automatic_Refinement/Lib/Refine_Lib"
        OptionHelpers
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
    ospec (DESTRimpl ni s) (\<lambda>r. \<exists>ni1 ni2. 
      r = (IFD v ni1 ni2) \<and> (ni1, n1) \<in> R s \<and> (ni2, n2) \<in> R s)"
begin

lemma les_refl[simp,intro!]:"les s s" by (auto simp add: les_def)
lemma les_trans[trans]:"les s1 s2 \<Longrightarrow> les s2 s3 \<Longrightarrow> les s1 s3" by (auto simp add: les_def)
lemmas DESTRimpl_rules = DESTRimpl_rule1 DESTRimpl_rule2 DESTRimpl_rule3

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
  apply (cases n; simp)
  unfolding case_ifexi_def
  apply (rule obind_rule)
  apply (rule DESTRimpl_rule1[OF INV, of ni])
  using NI apply simp apply simp apply (erule FTI)
  
  apply (rule obind_rule)
  apply (rule DESTRimpl_rule2[OF INV, of ni])
  using NI apply simp apply simp apply (erule FFI)

  apply (rule obind_rule)
  apply (rule DESTRimpl_rule3[OF INV, of ni])
  using NI apply simp apply clarsimp apply (erule (2) FII)
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
       }) e s
   "

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
  by (induction l rule: lowest_tops.induct) (auto split: option.splits)

lemma lowest_tops_impl_R: 
  assumes "list_all2 (in_rel (R s)) li l" "I s"
  shows "ospec (lowest_tops_impl li s) (\<lambda>(r,s'). r = lowest_tops l \<and> s'=s)"
  unfolding lowest_tops_alt
  using assms
  apply (induction rule: list_all2_induct)
  apply (simp add: lowest_tops_impl.simps)
  apply (simp add: lowest_tops_impl.simps)
  apply (rule case_ifexi_rule[where Q="\<lambda>s. Id", unfolded pair_in_Id_conv])
  apply assumption+
  apply (rule obind_rule)
  apply assumption
  apply (clarsimp split: option.splits)
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
  apply simp_all
  done

lemma restrict_top_impl_spec: "I s \<Longrightarrow> (ni,n) \<in> R s \<Longrightarrow> ospec (restrict_top_impl ni vr vl s) (\<lambda>(res,s'). (res, restrict_top n vr vl) \<in> R s \<and> s'=s)"
  unfolding restrict_top_impl_def restrict_top_alt
  apply (rule case_ifexi_rule[where I'="\<lambda>s'. s'=s" and Q="R", simplified])
  apply assumption+
  apply simp
  apply simp
  apply simp
  done  

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
proof(induction i t e arbitrary: s ii ti ei rule: ifex_ite.induct)
	case goal1 
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
	apply(assumption)+
	apply(simp)
	apply(simp)
	using None apply(simp)
	using None apply(clarsimp split: prod.splits ifex.splits)
done
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
	using les_def les_trans apply blast+
	done
qed
qed

lemma case_ifexi_mono[partial_function_mono]:
  assumes [partial_function_mono]: 
    "mono_option (\<lambda>F. fti F s)"
    "mono_option (\<lambda>F. ffi F s)"
    "\<And>x31 x32 x33. mono_option (\<lambda>F. fii F x31 x32 x33 s)"
  shows "mono_option (\<lambda>F. case_ifexi (fti F) (ffi F) (fii F) ni s)"
  unfolding case_ifexi_def
  apply (tactic \<open>Partial_Function.mono_tac @{context} 1\<close>)
  done

partial_function(option) val_impl :: "'ni \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> (bool\<times>'s) option"
where
"val_impl e ass s = case_ifexi
	(\<lambda>s. Some (True,s))
	(\<lambda>s. Some (False,s)) 
	(\<lambda>v t e s. val_impl (if ass v then t else e) ass s)
	e	s"

lemma "I s \<Longrightarrow> (ni,n) \<in> R s \<Longrightarrow> ospec (val_impl ni ass s) (\<lambda>(r,s'). r = (val_ifex n ass) \<and> s'=s)"
  apply (induction n arbitrary: ni)
  apply (subst val_impl.simps)
  apply (rule ospec_cons)
  apply (rule case_ifexi_rule[where I'="\<lambda>s'. s'=s" and Q="\<lambda>s. Id"]; assumption?)
  apply simp
  apply simp
  apply simp
  apply simp

  apply (subst val_impl.simps)
  apply (rule ospec_cons)
  apply (rule case_ifexi_rule[where I'="\<lambda>s'. s'=s" and Q="\<lambda>s. Id"]; assumption?)
  apply simp
  apply clarsimp apply simp
  apply simp
  apply simp

  apply (subst val_impl.simps)
  apply (subst val_ifex.simps)
  apply (clarsimp; intro impI conjI)
  apply (rule ospec_cons)
  apply (rule case_ifexi_rule[where I'="\<lambda>s'. s'=s" and Q="\<lambda>s. Id"]; assumption?)
  apply simp
  apply simp
  apply simp
  apply (rule ospec_cons)
  apply (rprems; simp)
  apply simp
  apply simp

  apply (rule ospec_cons)
  apply (rule case_ifexi_rule[where I'="\<lambda>s'. s'=s" and Q="\<lambda>s. Id"]; assumption?)
  apply simp
  apply simp
  apply simp
  apply (rule ospec_cons)
  apply (rprems; simp)
  apply simp
  apply simp
  done  

term IFimpl
  end

(* How do I get 'ni in here? *)
locale bdd_impl_cmp = bdd_impl +
  fixes cmp :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  assumes cmp_rule1: "I s \<Longrightarrow> (ni, i) \<in> R s \<Longrightarrow> (ni', i) \<in> R s \<Longrightarrow> cmp ni ni'"
  assumes cmp_rule2: "I s \<Longrightarrow> cmp ni ni' \<Longrightarrow> (ni, i) \<in> R s \<Longrightarrow> (ni', i) \<in> R s"
begin

fun param_opt_impl where
  "param_opt_impl i t e s =  do {
    id \<leftarrow> DESTRimpl i s;
    td \<leftarrow> DESTRimpl t s;
    ed \<leftarrow> DESTRimpl e s;
    (tn,s) \<leftarrow> Timpl s;
    (fn,s) \<leftarrow> Fimpl s;
    Some ((if id = TD then Some t else
    if id = FD then Some e else
    if td = TD \<and> ed = FD then Some i else
    if cmp t e then Some t else
    if ed = TD \<and> cmp i t then Some t else
    if td = FD \<and> cmp i e then Some e else
    None), s)}"

lemma param_opt_impl_R: 
  assumes "I s" "(ii,i) \<in> R s" "(ti,t) \<in> R s" "(ei,e) \<in> R s"
  shows "ospec (param_opt_impl ii ti ei s) 
               (\<lambda>(r,s'). case r of None \<Rightarrow> param_opt i t e = None
                                 | Some r \<Rightarrow> (param_opt i t e  = Some r' \<and> (r, r') \<in> R s)
                \<and> s = s')"
oops (* TODO *)


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

lemma ite_impl_opt_R: "
  I s
  \<Longrightarrow> in_rel (R s) ii i \<Longrightarrow> in_rel (R s) ti t \<Longrightarrow> in_rel (R s) ei e
  \<Longrightarrow> ospec (ite_impl_opt ii ti ei s) (\<lambda>(r, s'). (r, ifex_ite_opt i t e) \<in> R s' \<and> I s' \<and> les s s')"
oops (* TODO *)

end

locale bdd_impl_invar = bdd_impl_cmp +
  assumes Fimpl_rule: "I s \<Longrightarrow> ospec (Fimpl s) (\<lambda>(ni, s'). s = s')"
  assumes Timpl_rule: "I s \<Longrightarrow> ospec (Timpl s) (\<lambda>(ni, s'). s = s')"
  assumes IFimpl_rule: "I s \<Longrightarrow> ospec (IFimpl v t e s) (\<lambda>(r', s'). r' = r \<and> s' = s'') \<Longrightarrow>
                                ospec (IFimpl v t e s'') (\<lambda>(r', s'). r' = r \<and> s' = s'')"
begin

thm ite_impl.fixp_induct
thm ifex_ite.induct

lemma ite_impl_state_fixp:
  "I s \<Longrightarrow> in_rel (R s) ii i \<Longrightarrow> in_rel (R s) ti t \<Longrightarrow> in_rel (R s) ei e
       \<Longrightarrow> ospec (ite_impl ii ti ei s) (\<lambda>(r', s'). s' = s'')
       \<Longrightarrow> ospec (ite_impl ii ti ei s'') (\<lambda>(r', s'). s' = s'')"
proof(induction i t e arbitrary: s ii ti ei s'' rule: ifex_ite.induct)
	case goal1
  have inR: "(ii,i) \<in> R s" using goal1 by simp
	have la2: "list_all2 (in_rel (R s)) [ii,ti,ei] [i,t,e]" using goal1(4-6) by simp
  have sR: "les s s''" using ite_impl_R[OF goal1(3,4,5,6)] goal1(7)
    by (auto dest!: ospecD2 simp del: ifex_ite.simps)
  have "I s''" using ite_impl_R[OF goal1(3,4,5,6)] goal1(7)
    by (auto dest!: ospecD2 simp del: ifex_ite.simps)
  from sR la2 have la2': "list_all2 (in_rel (R s'')) [ii,ti,ei] [i,t,e]" using les_def by auto
	show ?case proof(cases "lowest_tops [i,t,e]")
		case None from goal1(3-6) show ?thesis
	apply(subst ite_impl.simps)
	apply(rule obind_rule[where Q="\<lambda>(r, s'). r = lowest_tops [i,t,e] \<and> s'=s''"])
	apply(rule ospec_cons)
	apply(rule lowest_tops_impl_R[OF la2'])
	using `I s''` apply(simp)
	apply(clarsimp split: prod.splits)
	apply(simp add: None split: prod.splits)
	apply(clarsimp)
	apply(rule ospec_cons)
	apply(rule case_ifexi_rule[where I'="\<lambda>s'. s'=s''"])
	using `I s''` apply(simp)
	using sR les_def apply(blast)
	apply(simp)
	apply(simp)
	using None apply(simp)
	using None apply(clarsimp split: prod.splits ifex.splits)
done
next
	case (Some lv)
	note mIH = goal1(1,2)[OF Some]
  thm goal1
	from goal1(3-6) show ?thesis
	apply(subst ite_impl.simps)
	apply(rule obind_rule[where Q="\<lambda>(r, s'). r = lowest_tops [i,t,e] \<and> s' = s''"])
	apply(rule ospec_cons)
	apply(rule lowest_tops_impl_R[OF la2'])
	using `I s''` apply(simp)
	apply(clarsimp split: prod.splits)
	apply(simp add: Some split: prod.splits)
	apply(clarsimp)
	(* take care of all those restrict_tops *) (* Yeah, i know, I'm to lazy to fix that now *)
          apply(rule obind_rule, rule restrict_top_impl_spec)
          using `I s''` apply(simp)
          using sR les_def apply(blast)
          apply(clarsimp split: prod.splits)
          apply(rule obind_rule, rule restrict_top_impl_spec)
          using `I s''` apply(simp)
          using sR les_def apply(blast)
          apply(clarsimp split: prod.splits)
          apply(rule obind_rule, rule restrict_top_impl_spec)
          using `I s''` apply(simp)
          using sR les_def apply(blast)
          apply(clarsimp split: prod.splits)
          apply(rule obind_rule, rule restrict_top_impl_spec)
          using `I s''` apply(simp)
          using sR les_def apply(blast)
          apply(clarsimp split: prod.splits)
          apply(rule obind_rule, rule restrict_top_impl_spec)
          using `I s''` apply(simp)
          using sR les_def apply(blast)
          apply(clarsimp split: prod.splits)
          apply(rule obind_rule, rule restrict_top_impl_spec)
          using `I s''` apply(simp)
          using sR les_def apply(blast)
          apply(clarsimp split: prod.splits)
  (* took care of restrict_tops *)
    apply(insert goal1(7)) apply(subst (asm) ite_impl.simps) 
    apply(subst (asm) ospec_bind_simp) apply(drule ospecD2) 
    apply(clarsimp) apply(insert lowest_tops_impl_R[OF la2]) 
    apply(clarsimp) using Some apply(auto)[1]
    thm ospecD2[OF restrict_top_impl_spec, of s]
    apply(subst (asm) ospec_bind_simp) apply(frule ospecD2[OF restrict_top_impl_spec, of s ii i lv True]; clarsimp)
    apply(subst (asm) ospec_bind_simp) apply(frule ospecD2[OF restrict_top_impl_spec, of s ti t lv True]; clarsimp)
    apply(subst (asm) ospec_bind_simp) apply(frule ospecD2[OF restrict_top_impl_spec, of s ei e lv True]; clarsimp)
    apply(subst (asm) ospec_bind_simp) apply(frule ospecD2[OF restrict_top_impl_spec, of s ii i lv False]; clarsimp)
    apply(subst (asm) ospec_bind_simp) apply(frule ospecD2[OF restrict_top_impl_spec, of s ti t lv False]; clarsimp)
    apply(subst (asm) ospec_bind_simp) apply(frule ospecD2[OF restrict_top_impl_spec, of s ei e lv False]; clarsimp)
  apply(rule obind_rule[where Q="\<lambda>(r, s'). s' = s''"])
  apply(rule mIH(1)[of s])
  apply(simp)
    apply(subgoal_tac "cmp a x1") using sR cmp_rule2 apply(auto)[1]
      using cmp_rule1 les_def sR `I s''` apply(meson)
    apply(subgoal_tac "cmp aa x1a") using sR cmp_rule2 apply(auto)[1]
      using cmp_rule1 les_def sR `I s''` apply(meson) 
    apply(subgoal_tac "cmp ab x1b") using sR cmp_rule2 apply(auto)[1]
      using cmp_rule1 les_def sR `I s''` apply(meson)
  thm ospecD2[OF ite_impl_R, of s x1 _ x1a _ x1b]



  


(*
  using goal1(7) apply(simp) apply(subst (asm) ite_impl.simps) apply(simp add: ospec_bind_simp)
   apply(drule ospecD2) apply(clarsimp) apply(insert lowest_tops_impl_R[OF la2])
   apply(clarsimp) using Some apply(auto)[1] apply(simp add: ospec_bind_simp) apply(drule ospecD2) 
   thm restrict_top_impl_spec[OF goal1(3) inR, of vr vl]
   apply(insert restrict_top_impl_spec[OF goal1(3) inR, of lv "True"]) apply(clarsimp)
   apply(subgoal_tac "cmp a x1") using cmp_rule2 apply(blast) 
   using les_def[of s s''] cmp_rule1[of s''] sR `I s''` apply(blast)

*)

oops
(*  defer
  apply(clarsimp split: prod.split)
  apply(rule obind_rule[where Q="\<lambda>(r, s'). s' = s''"])
  defer
  apply(clarsimp split: prod.split)



  apply(simp; fail)+
  apply(rule obind_rule)
  apply(rule mIH(1))
  apply(simp; fail)+ *)
(*	apply(rule obind_rule)
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
	using les_def les_trans apply blas *)
	done
end
end

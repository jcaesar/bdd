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

  end

(* How do I get 'ni in here? *)
locale bdd_impl_cmp = bdd_impl +
  fixes cmp :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  fixes Tni :: "'b"
  fixes Fni :: "'b"
  assumes tni_rule: "I s \<Longrightarrow> (Tni, Trueif) \<in> R s"
  assumes fni_rule: "I s \<Longrightarrow> (Fni, Falseif) \<in> R s"
  assumes cmp_rule1: "I s \<Longrightarrow> (ni, i) \<in> R s \<Longrightarrow> (ni', i) \<in> R s \<Longrightarrow> cmp ni ni'"
  assumes cmp_rule2: "I s \<Longrightarrow> cmp ni ni' \<Longrightarrow> (ni, i) \<in> R s \<Longrightarrow> (ni', i) \<in> R s"
begin

lemma tni_subst: "I s \<Longrightarrow> (ni, Trueif) \<in> R s \<longleftrightarrow> cmp Tni ni"
  using tni_rule1 cmp_rule1 cmp_rule2 by blast

lemma fni_subst: "I s \<Longrightarrow> (ni, Falseif) \<in> R s \<longleftrightarrow> cmp Fni ni"
  using fni_rule1 cmp_rule1 cmp_rule2 by blast


partial_function(option) ite_impl_opt where
"ite_impl_opt i t e s = 
  (if tni i then Some (t,s) else
  (if fni i then Some (e,s) else
  (if tni t \<and> fni e then Some (i,s) else
  (if cmp t e then Some (t,s) else
  (if cmp 
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
)}))))"

(*
lemma ite_impl_opt_R: "I s \<Longrightarrow> ite_impl_opt ii ti ei s = Some (r, s')
       \<Longrightarrow> in_rel (R s) ii i \<Longrightarrow> in_rel (R s) ti t \<Longrightarrow> in_rel (R s) ei e
       \<Longrightarrow> les s s' \<and> (r, ifex_ite_opt i t e) \<in> R s' \<and> I s'"
proof(induction i t e arbitrary: s s' ii ti ei r rule: ifex_ite_induct)
case(Trueif i t e)
  then have "lowest_tops_impl [ii, ti, ei] s = None" and "DESTRimpl ii s = TD"  
      by (case_tac[!] i, case_tac[!] t, case_tac[!] e,
         (fastforce dest: DESTRimpl_rules[OF \<open>I s\<close>] split: IFEXD.split)+)
  with Trueif show ?case  by(auto simp add: ite_impl_opt.simps)
next
case(Falseif i t e)
  then have "lowest_tops_impl [ii, ti, ei] s = None" and "DESTRimpl ii s = FD"  
    by (case_tac[!] i, case_tac[!] t, case_tac[!] e,
       (fastforce dest: DESTRimpl_rules[OF \<open>I s\<close>] split: IFEXD.split)+)
  with Falseif show ?case by(auto simp add: ite_impl_opt.simps)
next
case (IF i t e a)
  show ?case
    proof(cases i)
      assume "i = Trueif"
      from IF(4) have "(r, ifex_ite_opt i t e) \<in> R s'" apply(subst (asm) ite_impl_opt.simps)
           using `i = Trueif` DESTRimpl_rule1[OF `I s`] `in_rel (R s) ii i` `in_rel (R s) ti t` 
           by (simp)
      moreover from IF(4) have "s = s'" apply(subst (asm) ite_impl_opt.simps)
           using `i = Trueif` DESTRimpl_rule1[OF `I s`] `in_rel (R s) ii i` `in_rel (R s) ti t` 
           by (simp)
      ultimately show ?case using `I s` by blast
    next
      assume "i = Falseif"
      from IF(4) have "(r, ifex_ite_opt i t e) \<in> R s'" apply(subst (asm) ite_impl_opt.simps)
           using `i = Falseif` DESTRimpl_rules[OF `I s`] `in_rel (R s) ii i` `in_rel (R s) ei e` 
           by (simp)
      moreover from IF(4) have "s = s'" apply(subst (asm) ite_impl_opt.simps)
           using `i = Falseif` DESTRimpl_rules[OF `I s`] `in_rel (R s) ii i` 
           by (simp)
      ultimately show ?case using `I s` by blast
    next
      fix iv ile iri assume "i = IF iv ile iri" 
      with `I s` `in_rel (R s) ii i` have iiDESTR: "\<exists>ni1 ni2. DESTRimpl ii s = IFD iv ni1 ni2"
        using DESTRimpl_rule3 by fastforce
      show ?case
        proof(cases "t = Trueif \<and> e = Falseif")
          assume Deq: "t = Trueif \<and> e = Falseif"
          from IF(4) have "s = s'" apply(subst (asm) ite_impl_opt.simps)
             using `i =  IF iv ile iri` DESTRimpl_rule3[OF `I s`, of ii iv ile iri ]
                   DESTRimpl_rule1[OF `I s`, of ti] DESTRimpl_rule2[OF `I s`, of ei]
                   `in_rel (R s) ii i` `in_rel (R s) ti t` `in_rel (R s) ei e` Deq by (auto)
           moreover from IF(4) have "(r, ifex_ite_opt i t e) \<in> R s'" 
             apply(subst (asm) ite_impl_opt.simps)
             using `i =  IF iv ile iri` DESTRimpl_rule3[OF `I s`, of ii iv ile iri ]
                 DESTRimpl_rule1[OF `I s`, of ti] DESTRimpl_rule2[OF `I s`, of ei]
                 `in_rel (R s) ii i` `in_rel (R s) ti t` `in_rel (R s) ei e` Deq by (auto)
           ultimately show ?case using `I s` by blast
         next
           assume Dneq: "\<not> (t = Trueif \<and> e = Falseif)"
               from this have ti_te_DESTR: "\<not> (DESTRimpl ti s = TD \<and> DESTRimpl ei s = FD)"
                 using DESTRimpl_rules[OF `I s`] `in_rel (R s) ti t` `in_rel (R s) ei e`
                 apply(case_tac t, case_tac[!] e) by (fastforce)+
                show ?case
             proof(cases "ti = ei")
               assume "ti = ei"
                 then have "t = e" using ifexd_eq[OF `I s`] `in_rel (R s) ti t` `in_rel (R s) ei e`
                   by auto
                 from IF(4) have "s = s'" apply(subst (asm) ite_impl_opt.simps) using iiDESTR
                               apply(auto) using ti_te_DESTR apply(auto) using `ti = ei` by auto
                 moreover from IF(4) have "(r, ifex_ite_opt i t e) \<in> R s'" 
                   apply(subst (asm) ite_impl_opt.simps) using iiDESTR
                   apply(auto)
                   using ti_te_DESTR apply(auto) using `ti = ei` apply(auto)
                   using `i =  IF iv ile iri` Dneq `t = e` `in_rel (R s) ei e`
                     by(auto simp del: ifex_ite_opt.simps restrict_top.simps lowest_tops.simps)
                  ultimately show ?case using `I s` by simp
         next
           assume "ti \<noteq> ei"
           then have "t \<noteq> e" using ifex_eq[OF `I s`]  `in_rel (R s) ti t` `in_rel (R s) ei e`
             by force
           have 0: "ite_impl_opt ii ti ei s = (case lowest_tops_impl [ii, ti, ei] s of None \<Rightarrow> Some (case DESTRimpl ii s of TD \<Rightarrow> (ti, s) | FD \<Rightarrow> (ei, s))
                     | Some a \<Rightarrow> let ti' = restrict_top_impl ii a True s; tt = restrict_top_impl ti a True s; te = restrict_top_impl ei a True s; fi = restrict_top_impl ii a False s;
                                     ft = restrict_top_impl ti a False s; fe = restrict_top_impl ei a False s
                                 in ite_impl_opt ti' tt te s \<guillemotright>= (\<lambda>(tb, s). ite_impl_opt fi ft fe s \<guillemotright>= (\<lambda>(fb, s). Some (IFimpl a tb fb s))))"
             apply(subst ite_impl_opt.simps) using iiDESTR `ti \<noteq> ei` ti_te_DESTR 
             by (auto simp del: lowest_tops_impl.simps)
           note inR = `in_rel (R s) ii i` `in_rel (R s) ti t` `in_rel (R s) ei e`
           from \<open>I s\<close> inR \<open>lowest_tops [i, t, e] = Some a\<close>
           have 1: "lowest_tops_impl [ii, ti, ei] s = Some a"
           by(case_tac[!] i, case_tac[!] t, case_tac[!] e,
             (fastforce dest: DESTRimpl_rules[OF \<open>I s\<close>] split: IFEXD.split)+)
           from IF obtain tb st
            where tb_def: "ite_impl_opt (restrict_top_impl ii a True s) (restrict_top_impl ti a True s)
                       (restrict_top_impl ei a True s) s = Some (tb, st)"
            by (auto simp: Option.bind_eq_Some_conv 1 0
                     simp del: restrict_top_impl.simps lowest_tops_impl.simps)
            from `ite_impl_opt ii ti ei s = Some (r, s')` obtain eb se
              where eb_def: "ite_impl_opt (restrict_top_impl ii a False s) (restrict_top_impl ti a False s)
                                 (restrict_top_impl ei a False s) st = Some (eb, se)"
              apply (subst (asm) 0)
              by(auto simp del: lowest_tops_impl.simps restrict_top_impl.simps
                      simp add: Option.bind_eq_Some_conv 1 tb_def)
            from `I s` inR IF(1)[OF \<open>I s\<close> tb_def, of True] have
              3: "(tb,
                   ifex_ite_opt (restrict_top i a True) (restrict_top t a True) (restrict_top e a True)) \<in> R st"
                 "les s st" "I st" by (auto dest: restrict_top_R simp del: restrict_top_impl.simps)
            from inR `les s st` IF(1)[OF `I st` eb_def, of False]
            have "(eb,
                  ifex_ite_opt (restrict_top i a False) (restrict_top t a False) (restrict_top e a False)) \<in> R se
                  \<and> les st se \<and> I se" unfolding les_def
            by(fastforce dest: restrict_top_R[OF `I s`, of ii i] restrict_top_R[OF `I s`, of ti t] restrict_top_R[OF `I s`, of ei e]
                       simp del: restrict_top_impl.simps restrict_top.simps ifex_ite.simps)
            then have 4:
              "(eb, ifex_ite_opt (restrict_top i a False) (restrict_top t a False) (restrict_top e a False)) \<in> R se"
              "les st se"
              "I se" by auto
            from IF(4) have 5: "ite_impl_opt ii ti ei s = Some (IFimpl a tb eb se)"
              apply(subst (asm) 0, subst (asm) 1,
                    auto simp del: restrict_top_impl.simps simp add: Option.bind_eq_Some_conv)
              using tb_def eb_def by auto
            from 3 4 les_def[of st se]
              have 6: "(tb, 
                     ifex_ite_opt (restrict_top i a True) (restrict_top t a True) (restrict_top e a True)) \<in> R se"
              by blast
            from IFimpl_mono[OF `I se` this, of _ _ a r s'] 4 5 IF have "les se s'" by force
            from IFimpl_inv[OF `I se` 6 4(1), of a r s'] 5 IF have "I s'" by auto
            from `les se s'` 3 4 les_trans have goal11: "les s s'" by blast
            from IF(2) `i = IF iv ile iri` `t \<noteq> e` Dneq
              have 7:
              "ifex_ite_opt i t e =
               IFC a (ifex_ite_opt (restrict_top i a True) (restrict_top t a True) (restrict_top e a True))
                (ifex_ite_opt (restrict_top i a False) (restrict_top t a False) (restrict_top e a False))"
              by (auto)
            from 5 IF(4) have "IFimpl a tb eb se = (r, s')" by force
            from goal11 IFimpl_rule[OF `I se` 6 4(1) this] `I s'` 7 show ?case
            by(auto split: ifc_split)
qed
qed
qed
qed
*)

end
end

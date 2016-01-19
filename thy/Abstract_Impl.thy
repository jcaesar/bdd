theory Abstract_Impl
imports BDT
        "~~/src/HOL/Library/Monad_Syntax"
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
  fixes Timpl :: "'s \<Rightarrow> ('ni \<times> 's)"
  fixes Fimpl :: "'s \<Rightarrow> ('ni \<times> 's)"
  fixes IFimpl :: "'a \<Rightarrow> 'ni \<Rightarrow> 'ni \<Rightarrow> 's \<Rightarrow> ('ni \<times> 's)"
  fixes DESTRimpl :: "'ni  \<Rightarrow> 's \<Rightarrow> ('a, 'ni) IFEXD"

  assumes Timpl_mono: "I s \<Longrightarrow> Timpl s = (ni, s') \<Longrightarrow> les s s'"
  assumes Fimpl_mono: "I s \<Longrightarrow> Fimpl s = (ni, s') \<Longrightarrow> les s s'"
  assumes IFimpl_mono: "\<lbrakk>I s; (ni1,n1) \<in> R s;(ni2,n2) \<in> R s; IFimpl v ni1 ni2 s = (ni, s')\<rbrakk>
                       \<Longrightarrow> les s s'"

  assumes Timpl_rule: "I s \<Longrightarrow> Timpl s = (ni, s') \<Longrightarrow> (ni, Trueif) \<in> R s'"
  assumes Fimpl_rule: "I s \<Longrightarrow> Fimpl s = (ni, s') \<Longrightarrow> (ni, Falseif) \<in> R s'"
  assumes IFimpl_rule: "\<lbrakk>I s; (ni1,n1) \<in> R s;(ni2,n2) \<in> R s; IFimpl v ni1 ni2 s = (ni, s')\<rbrakk>
                       \<Longrightarrow> (ni, IFC v n1 n2) \<in> R s'"

  assumes DESTRimpl_rule1: "I s \<Longrightarrow> (ni, Trueif) \<in> R s \<Longrightarrow> DESTRimpl ni s = TD"
  assumes DESTRimpl_rule2: "I s \<Longrightarrow> (ni, Falseif) \<in> R s \<Longrightarrow> DESTRimpl ni s = FD"
  assumes DESTRimpl_rule3: "I s \<Longrightarrow> (ni, IF v n1 n2) \<in> R s \<Longrightarrow> \<exists>ni1 ni2. DESTRimpl ni s = IFD v ni1 ni2 
                                                       \<and> (ni1, n1) \<in> R s \<and> (ni2, n2) \<in> R s"

  assumes Timpl_inv: "I s \<Longrightarrow> Timpl s = (ni, s') \<Longrightarrow> I s'"
  assumes Fimpl_inv: "I s \<Longrightarrow> Fimpl s = (ni, s') \<Longrightarrow> I s'"
  assumes IFimpl_inv: "\<lbrakk>I s; (ni1,n1) \<in> R s;(ni2,n2) \<in> R s; IFimpl v ni1 ni2 s = (ni, s')\<rbrakk> \<Longrightarrow> I s'"
begin

lemma les_refl[simp,intro!]:"les s s" by (auto simp add: les_def)
lemma les_trans[trans]:"les s1 s2 \<Longrightarrow> les s2 s3 \<Longrightarrow> les s1 s3" by (auto simp add: les_def)

fun lowest_tops_impl where
"lowest_tops_impl [] s = None" |
"lowest_tops_impl (e#es) s = 
	(case DESTRimpl e s of
		(IFD v t e) \<Rightarrow> (case lowest_tops_impl es s of 
			Some u \<Rightarrow> Some (min u v) | 
			None \<Rightarrow> Some v) |
		_           \<Rightarrow> lowest_tops_impl es s)"

fun restrict_top_impl where
"restrict_top_impl e vr vl s = (case DESTRimpl e s of
	IFD v te ee \<Rightarrow> (if v = vr then (if vl then te else ee) else e) |
	_ \<Rightarrow> e)"

lemma restrict_top_R: "I s \<Longrightarrow> (ni,i) \<in> R s \<Longrightarrow>
                       (restrict_top_impl ni vr vl s, restrict_top i vr vl) \<in> R s"
by (induction i vr vl rule: restrict_top.induct,
    auto dest: DESTRimpl_rule1 DESTRimpl_rule2 DESTRimpl_rule3)

partial_function(option) ite_impl where
"ite_impl i t e s = 
	(case lowest_tops_impl [i, t, e] s of
		Some a \<Rightarrow> (let
			ti = restrict_top_impl i a True s;
			tt = restrict_top_impl t a True s;
			te = restrict_top_impl e a True s;
			fi = restrict_top_impl i a False s;
			ft = restrict_top_impl t a False s;
			fe = restrict_top_impl e a False s
			in do {
			(tb,s) \<leftarrow> ite_impl ti tt te s;
			(fb,s) \<leftarrow> ite_impl fi ft fe s;
            Some (IFimpl a tb fb s)}) |
        None \<Rightarrow> Some (case DESTRimpl i s of TD \<Rightarrow> (t, s) | FD \<Rightarrow> (e, s)))"


lemma ite_impl_R: "I s \<Longrightarrow> ite_impl ii ti ei s = Some (r, s')
       \<Longrightarrow> in_rel (R s) ii i \<Longrightarrow> in_rel (R s) ti t \<Longrightarrow> in_rel (R s) ei e
       \<Longrightarrow> les s s' \<and> (r, ifex_ite i t e) \<in> R s' \<and> I s'"
proof(induction i t e arbitrary: s s' ii ti ei r rule: ifex_ite_induct)
case (goal3 i t e a)
  print_cases
  note IFCase = goal3
  note inR = `in_rel (R s) ii i` `in_rel (R s) ti t` `in_rel (R s) ei e`
  from \<open>I s\<close> inR \<open>lowest_tops [i, t, e] = Some a\<close>
    have 0: "lowest_tops_impl [ii, ti, ei] s = Some a"
    by(case_tac[!] i, case_tac[!] t, case_tac[!] e,
       (fastforce dest: DESTRimpl_rule1[OF \<open>I s\<close>] DESTRimpl_rule2[OF \<open>I s\<close>] DESTRimpl_rule3[OF \<open>I s\<close>]
                  split: IFEXD.split)+) (* takes quite a while *)
  from IFCase obtain tb st
    where tb_def: "ite_impl (restrict_top_impl ii a True s) (restrict_top_impl ti a True s)
                       (restrict_top_impl ei a True s) s = Some (tb, st)"
    by (auto simp: Option.bind_eq_Some_conv 0 ite_impl.simps
             simp del: restrict_top_impl.simps lowest_tops_impl.simps)
  from `ite_impl ii ti ei s = Some (r, s')` obtain eb se
    where eb_def: "ite_impl (restrict_top_impl ii a False s) (restrict_top_impl ti a False s)
                       (restrict_top_impl ei a False s) st = Some (eb, se)"
    by (subst (asm) (2) ite_impl.simps,
        auto simp del: lowest_tops_impl.simps restrict_top_impl.simps
             simp add: Option.bind_eq_Some_conv 0 tb_def)
  from `I s` inR IFCase(1)[OF \<open>I s\<close> tb_def, of True] have
    3: "(tb,
         ifex_ite (restrict_top i a True) (restrict_top t a True) (restrict_top e a True)) \<in> R st"
       "les s st" "I st" by (auto dest: restrict_top_R simp del: restrict_top_impl.simps)
  from inR `les s st` IFCase(1)[OF `I st` eb_def, of False]
  have 4: "(eb,
        ifex_ite (restrict_top i a False) (restrict_top t a False) (restrict_top e a False)) \<in> R se"
        "les st se" "I se" unfolding les_def
  apply(fastforce dest: restrict_top_R[OF `I s`, of ii i] restrict_top_R[OF `I s`, of ti t] restrict_top_R[OF `I s`, of ei e]
             simp del: restrict_top_impl.simps restrict_top.simps ifex_ite.simps) sorry
  from IFCase(4) have 5: "ite_impl ii ti ei s = Some (IFimpl a tb eb se)"
    apply(subst (asm) ite_impl.simps, subst (asm) 0,
          auto simp del: restrict_top_impl.simps simp add: Option.bind_eq_Some_conv)
    using tb_def eb_def by auto
  from 3 4 les_def[of st se]
    have 6: "(tb, 
           ifex_ite (restrict_top i a True) (restrict_top t a True) (restrict_top e a True)) \<in> R se"
    by blast
  from IFimpl_mono[OF `I se` this, of _ _ a r s'] 4 5 IFCase have "les se s'" by force
  from IFimpl_inv[OF `I se` 6 4(1), of a r s'] 5 IFCase have "I s'" by auto
  from `les se s'` 3 4 les_trans have goal11: "les s s'" by blast
  from IFCase(2)
    have 7:
    "ifex_ite i t e =
     IFC a (ifex_ite (restrict_top i a True) (restrict_top t a True) (restrict_top e a True))
      (ifex_ite (restrict_top i a False) (restrict_top t a False) (restrict_top e a False))"
    by simp
  from 5 IFCase(4) have "IFimpl a tb eb se = (r, s')" by force
  from goal11 IFimpl_rule[OF `I se` 6 4(1) this] `I s'` 7 show ?case
  by(auto split: ifc_split)
next
case("1" i t e) note TrueIFCase = "1"
  from this
    have 0: "lowest_tops_impl [ii, ti, ei] s = None"
            "DESTRimpl ii s = TD"  
      by (case_tac[!] i, case_tac[!] t, case_tac[!] e,
         (fastforce dest: DESTRimpl_rule1[OF \<open>I s\<close>] DESTRimpl_rule2[OF \<open>I s\<close>] DESTRimpl_rule3[OF \<open>I s\<close>]
                    split: IFEXD.split)+)
  from this TrueIFCase have 1: "r = ti" by(auto simp add: ite_impl.simps)
  from 0 TrueIFCase have    2: "s = s'" by(auto simp add: ite_impl.simps)
  from TrueIFCase have 3: "ifex_ite i t e = t" by simp
  from les_refl 1 2 3 TrueIFCase show ?case by auto
next
case("2" i t e) note FalseIFCase = "2"
    from this
    have 0: "lowest_tops_impl [ii, ti, ei] s = None"
            "DESTRimpl ii s = FD"  
      by (case_tac[!] i, case_tac[!] t, case_tac[!] e,
         (fastforce dest: DESTRimpl_rule1[OF \<open>I s\<close>] DESTRimpl_rule2[OF \<open>I s\<close>] DESTRimpl_rule3[OF \<open>I s\<close>]
                    split: IFEXD.split)+)
  from this FalseIFCase have 1: "r = ei" by(auto simp add: ite_impl.simps)
  from 0 FalseIFCase have    2: "s = s'" by(auto simp add: ite_impl.simps)
  from FalseIFCase have 3: "ifex_ite i t e = e" by simp
  from 1 2 3 FalseIFCase show ?case by auto
qed

partial_function(option) val_impl :: "'ni \<Rightarrow> 's \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool option" 
where
"val_impl e s ass = (case (DESTRimpl e s) of
	TD \<Rightarrow> Some True |
	FD \<Rightarrow> Some False |
	(IFD v t e) \<Rightarrow> val_impl (if ass v then t else e) s ass)"

lemma "I s \<Longrightarrow> (ni,n) \<in> R s \<Longrightarrow> Some (val_ifex n ass) = val_impl ni s ass"
by (induction n arbitrary: ni, 
    auto dest: DESTRimpl_rule1 DESTRimpl_rule2 DESTRimpl_rule3 simp add: val_impl.simps)

end
end
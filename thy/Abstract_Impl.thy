theory Abstract_Impl
imports BDT
        "~~/src/HOL/Library/Monad_Syntax"
begin

datatype ('a, 'ni) IFEXD = TD | FD | IFD 'a 'ni 'ni 

locale bdd_impl = 
  fixes R :: "'s \<Rightarrow> ('ni \<times> 'a ifex) set"
  fixes Timpl :: "'s \<Rightarrow> ('ni \<times> 's)"
  fixes Fimpl :: "'s \<Rightarrow> ('ni \<times> 's)"
  fixes IFimpl :: "'a \<Rightarrow> 'ni \<Rightarrow> 'ni \<Rightarrow> 's \<Rightarrow> ('ni \<times> 's)"
  fixes DESTRimpl :: "'ni  \<Rightarrow> 's \<Rightarrow> ('a, 'ni) IFEXD"

  fixes les :: "'s \<Rightarrow> 's \<Rightarrow> bool"
  defines "les s s' == \<forall>ni n. (ni, n) \<in> R s \<longrightarrow> (ni, n) \<in> R s'"

  assumes Timpl_mono: "Timpl s = (ni, s') \<Longrightarrow> les s s'"
  assumes Fimpl_mono: "Fimpl s = (ni, s') \<Longrightarrow> les s s'"
  assumes IFimpl_mono: "\<lbrakk>(ni1,n1) \<in> R s;(ni2,n2) \<in> R s; IFimpl v ni1 ni2 s = (ni, s')\<rbrakk>
                       \<Longrightarrow> les s s'"

  assumes Timpl_rule: "Timpl s = (ni, s') \<Longrightarrow> (ni, Trueif) \<in> R s'"
  assumes Fimpl_rule: "Fimpl s = (ni, s') \<Longrightarrow> (ni, Falseif) \<in> R s'"
  assumes IFimpl_rule: "\<lbrakk>(ni1,n1) \<in> R s;(ni2,n2) \<in> R s; IFimpl v ni1 ni2 s = (ni, s')\<rbrakk>
                       \<Longrightarrow> (ni, IF v n1 n2) \<in> R s'"

  assumes DESTRimpl_rule1: "(ni, Trueif) \<in> R s \<Longrightarrow> DESTRimpl ni s = TD"
  assumes DESTRimpl_rule2: "(ni, Falseif) \<in> R s \<Longrightarrow> DESTRimpl ni s = FD"
  assumes DESTRimpl_rule3: "(ni, IF v n1 n2) \<in> R s \<Longrightarrow> \<exists>ni1 ni2. DESTRimpl ni s = IFD v ni1 ni2 
                                                       \<and> (ni1, n1) \<in> R s \<and> (ni2, n2) \<in> R s"

begin


function restrict_impl where
  "restrict_impl n var val s = (case DESTRimpl n s of
                                    (IFD v t e) \<Rightarrow> (let (rt,s) = restrict_impl t var val s;
                                                        (re,s) = restrict_impl e var val s in
                                                     if v = var then (if val then (rt,s) else (re, s)) else
                                                     (IFimpl v rt re s)) |
                                     i \<Rightarrow> (n,s))"
by pat_completeness auto

partial_function(option) restrict_impl_opt where
  "restrict_impl_opt n var val s = (case DESTRimpl n s of
                                    (IFD v t e) \<Rightarrow> (do {(rt,s) \<leftarrow> restrict_impl_opt t var val s;
                                                        (re,s) \<leftarrow> restrict_impl_opt e var val s;
                                                     if v = var then (if val then Some (rt,s) else Some (re, s)) else
                                                     Some (IFimpl v rt re s)}) |
                                     i \<Rightarrow> Some (n,s))"

lemma les_refl[simp,intro!]:"les s s" by (auto simp add: les_def)
lemma les_trans[trans]:"les s1 s2 \<Longrightarrow> les s2 s3 \<Longrightarrow> les s1 s3" by (auto simp add: les_def)


lemma "(ni, n) \<in> R s \<Longrightarrow> \<exists>rni s'. restrict_impl_opt ni var val s = Some (rni, s') \<and> 
                          (rni, restrict n var val) \<in> R s' \<and> les s s'"
apply(induction n arbitrary: ni s)
apply(simp) apply(subst restrict_impl_opt.simps) apply(frule DESTRimpl_rule1) apply(simp)
apply(simp) apply(subst restrict_impl_opt.simps) apply(frule DESTRimpl_rule2) apply(simp)
apply(simp split del: split_if) apply(subst restrict_impl_opt.simps) apply(frule DESTRimpl_rule3) 
apply(clarsimp split del: split_if)
proof -
	case goal1
	note goal1(1)[OF goal1(5)]
	then obtain rnit s' where rnits: "restrict_impl_opt ni1 var val s = Some (rnit, s')" "(rnit, restrict n1 var val) \<in> R s'" "les s s'" by blast
	from this(3) goal1(6) have "(ni2, n2) \<in> R s'" unfolding les_def by simp
	note goal1(2)[OF this]
	then obtain rnie s'' where rnies: "restrict_impl_opt ni2 var val s' = Some (rnie, s'')" "(rnie, restrict n2 var val) \<in> R s''"  "les s' s''" by blast
	from this(3) rnits(2) have 1: "(rnit, restrict n1 var val) \<in> R s''" unfolding les_def by simp
	obtain r s''' where rs: "IFimpl x1 rnit rnie s'' = (r,s''')" by force
	have les: "les s s'''" using les_trans rnits(3) rnies(3) IFimpl_mono[OF 1 rnies(2) rs] by blast
	show ?case
		unfolding rnits(1)
		unfolding bind_lunit
		apply(split prod.splits, clarify)
	unfolding rnies(1)
	unfolding bind_lunit
	apply(split prod.splits, clarify)
	apply(cases  "x1 = var")
	apply(simp only: refl if_True)
	using les_def rnies rnits apply auto[1]
	apply(simp only: refl if_False)
	apply simp
	apply rule
	apply rule
	apply(rule)
	apply(simp add: rs)
	using les IFimpl_rule[OF 1 rnies(2) rs]
	apply simp
	done
qed

end
end
theory Abstract_Impl
imports BDT
        "~~/src/HOL/Library/Monad_Syntax"
begin

datatype ('a, 'ni) IFEXD = TD | FD | IFD 'a 'ni 'ni 

locale bdd_impl = 
  fixes R :: "'s \<Rightarrow> ('ni \<times> ('a :: linorder) ifex) set"
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
                                     _ \<Rightarrow> Some (n,s))"

lemma les_refl[simp,intro!]:"les s s" by (auto simp add: les_def)
lemma les_trans[trans]:"les s1 s2 \<Longrightarrow> les s2 s3 \<Longrightarrow> les s1 s3" by (auto simp add: les_def)


lemma "(ni, n) \<in> R s \<Longrightarrow> \<exists>rni s'. restrict_impl_opt ni var val s = Some (rni, s') \<and> 
                          (rni, restrict n var val) \<in> R s' \<and> les s s'"
proof(induction n arbitrary: ni s)
	case goal3
	note DESTRimpl_rule3[OF goal3(3)] then obtain ni1 ni2 where dimp: "DESTRimpl ni s = IFD x1 ni1 ni2" and ni1: "(ni1, n1) \<in> R s" and ni2: "(ni2, n2) \<in> R s" by blast
	note goal3(1)[OF ni1]
	then obtain rnit s' where rnits: "restrict_impl_opt ni1 var val s = Some (rnit, s')" "(rnit, restrict n1 var val) \<in> R s'" "les s s'" by blast
	from this(3) ni2 have "(ni2, n2) \<in> R s'" unfolding les_def by simp
	note goal3(2)[OF this]
	then obtain rnie s'' where rnies: "restrict_impl_opt ni2 var val s' = Some (rnie, s'')" "(rnie, restrict n2 var val) \<in> R s''"  "les s' s''" by blast
	from this(3) rnits(2) have 1: "(rnit, restrict n1 var val) \<in> R s''" unfolding les_def by simp
	obtain r s''' where rs: "IFimpl x1 rnit rnie s'' = (r,s''')" by force
	have les: "les s s''" "les s s'''" using les_trans rnits(3) rnies(3) IFimpl_mono[OF 1 rnies(2) rs] by blast+
	show ?case
		using 1 rnies(2) les IFimpl_rule[OF 1 rnies(2) rs]
		by(subst restrict_impl_opt.simps, auto simp add: rnits(1) rnies(1) dimp rs)
qed (force dest: DESTRimpl_rule1 DESTRimpl_rule2 simp add: restrict_impl_opt.simps)+

fun lowest_tops_impl where
"lowest_tops_impl [] s = None" |
"lowest_tops_impl (e#es) s = 
	(case DESTRimpl e s of
		(IFD v t e) \<Rightarrow> (case lowest_tops_impl es s of 
			Some u \<Rightarrow> Some (min u v) | 
			None \<Rightarrow> Some v) |
		_           \<Rightarrow> lowest_tops_impl es s)"
fun in_R_list where
"in_R_list nis [] _ = (case nis of (_#_) \<Rightarrow> False | _ \<Rightarrow> True)" |
"in_R_list nis (n#ns) s = (case nis of (ni#nis) \<Rightarrow> ((ni, n) \<in> R s) \<and> in_R_list nis ns s | _ \<Rightarrow> False)"
lemma in_R_list_split: "in_R_list (ni#nis) (n#ns) s \<Longrightarrow> ((ni, n) \<in> R s \<and> in_R_list nis ns s)"
by simp

lemma in_R_list_lt: "in_R_list nis ns s \<Longrightarrow> lowest_tops_impl nis s = lowest_tops ns"
apply(induction rule: lowest_tops.induct)
apply(simp split: list.splits)
defer
apply(simp split: list.splits)
sorry (* todo (probably) *)

lemma DESTR_vareq: "(ni,IF v t e) \<in> R s \<Longrightarrow> DESTRimpl ni s = IFD nv nt ne \<Longrightarrow> nv = v"
	by(drule DESTRimpl_rule3, simp)

fun restrict_top_impl where
"restrict_top_impl e vr vl s = (case DESTRimpl e s of
	IFD v te ee \<Rightarrow> (if v = vr then (if vl then te else ee) else e) |
	_ \<Rightarrow> e)"
lemma restrict_top_R[intro]: "(ni,i) \<in> R s \<Longrightarrow> (restrict_top_impl ni vr vl s, restrict_top i vr vl) \<in> R s"
apply(induction i vr vl rule: restrict_top.induct) defer
apply(simp_all add: DESTRimpl_rule1 DESTRimpl_rule2)[2]
apply(simp only: restrict_top.simps restrict_top_impl.simps)
apply(case_tac "v = var")
apply(simp only: refl if_True)
apply(drule DESTRimpl_rule3)
apply fastforce
apply(simp only: if_False split: if_splits IFEXD.splits)
apply(simp)
apply(blast dest: DESTR_vareq)
done

(* todo: write restrict_top and use it! (also, that doesn't return state) *)
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
lemma "
	ite_impl ii ti ei s = Some (r, s') \<Longrightarrow>
	in_R_list [ii, ti, ei] [i, t, e] s \<Longrightarrow>
	(r, ifex_ite i t e) \<in> R s'"
apply(induction i t e rule: ifex_ite_induct)
apply(simp del: lowest_tops.simps in_R_list.simps)
apply(frule in_R_list_lt)
apply(subst(asm) ite_impl.simps)
apply(simp only: refl split: option.splits list.splits)
apply(clarsimp simp del: lowest_tops_impl.simps lowest_tops.simps in_R_list.simps)
apply(drule in_R_list_split, clarify)+
apply(drule DESTRimpl_rule1)
apply(simp_all)[2]
apply(simp del: lowest_tops.simps in_R_list.simps)
apply(frule in_R_list_lt)
apply(subst(asm) ite_impl.simps)
apply(simp only: refl split: option.splits list.splits)
apply(clarsimp simp del: lowest_tops_impl.simps lowest_tops.simps in_R_list.simps)
apply(drule in_R_list_split, clarify)+
apply(drule DESTRimpl_rule2)
apply(simp_all)[2]
apply(subst(asm) ite_impl.simps)
apply(frule in_R_list_lt)
apply(simp only: Let_def bind_eq_Some_conv split: option.splits)
apply(drule in_R_list_split, clarify)+
apply(drule restrict_top_R[of ii])
apply(drule restrict_top_R[of ti])
apply(drule restrict_top_R[of ei])
find_theorems "(_ \<guillemotright>= _) = Some _"
oops (* we have work to do *)

end
end
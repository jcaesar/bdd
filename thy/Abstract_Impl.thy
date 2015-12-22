theory Abstract_Impl
imports BDT
        "~~/src/HOL/Library/Monad_Syntax"
begin

datatype ('a, 'ni) IFEXD = TD | FD | IFD 'a 'ni 'ni 

locale bdd_impl_pre =
  fixes R :: "'s \<Rightarrow> ('ni \<times> ('a :: linorder) ifex) set"
begin
  definition les:: "'s \<Rightarrow> 's \<Rightarrow> bool" where
  "les s s' == \<forall>ni n. (ni, n) \<in> R s \<longrightarrow> (ni, n) \<in> R s'"
end


locale bdd_impl = bdd_impl_pre R for R :: "'s \<Rightarrow> ('ni \<times> ('a :: linorder) ifex) set" +
  fixes Timpl :: "'s \<Rightarrow> ('ni \<times> 's)"
  fixes Fimpl :: "'s \<Rightarrow> ('ni \<times> 's)"
  fixes IFimpl :: "'a \<Rightarrow> 'ni \<Rightarrow> 'ni \<Rightarrow> 's \<Rightarrow> ('ni \<times> 's)"
  fixes DESTRimpl :: "'ni  \<Rightarrow> 's \<Rightarrow> ('a, 'ni) IFEXD"

  assumes Timpl_mono: "Timpl s = (ni, s') \<Longrightarrow> les s s'"
  assumes Fimpl_mono: "Fimpl s = (ni, s') \<Longrightarrow> les s s'"
  assumes IFimpl_mono: "\<lbrakk>(ni1,n1) \<in> R s;(ni2,n2) \<in> R s; IFimpl v ni1 ni2 s = (ni, s')\<rbrakk>
                       \<Longrightarrow> les s s'"

  assumes Timpl_rule: "Timpl s = (ni, s') \<Longrightarrow> (ni, Trueif) \<in> R s'"
  assumes Fimpl_rule: "Fimpl s = (ni, s') \<Longrightarrow> (ni, Falseif) \<in> R s'"
  assumes IFimpl_rule: "\<lbrakk>(ni1,n1) \<in> R s;(ni2,n2) \<in> R s; IFimpl v ni1 ni2 s = (ni, s')\<rbrakk>
                       \<Longrightarrow> (ni, IFC v n1 n2) \<in> R s'"

  assumes DESTRimpl_rule1: "(ni, Trueif) \<in> R s \<Longrightarrow> DESTRimpl ni s = TD"
  assumes DESTRimpl_rule2: "(ni, Falseif) \<in> R s \<Longrightarrow> DESTRimpl ni s = FD"
  assumes DESTRimpl_rule3: "(ni, IF v n1 n2) \<in> R s \<Longrightarrow> \<exists>ni1 ni2. DESTRimpl ni s = IFD v ni1 ni2 
                                                       \<and> (ni1, n1) \<in> R s \<and> (ni2, n2) \<in> R s"

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
fun in_R_list where
"in_R_list (ni#nis) (n#ns) s = (((ni, n) \<in> R s) \<and> in_R_list nis ns s)" |
"in_R_list [] [] _ = True" |
"in_R_list _ _ _ = False"
lemma in_R_list_split: "in_R_list (ni#nis) (n#ns) s \<Longrightarrow> ((ni, n) \<in> R s \<and> in_R_list nis ns s)"
by simp

lemma in_R_list_lt: "in_R_list nis ns s \<Longrightarrow> lowest_tops_impl nis s = lowest_tops ns"
apply(induction rule: in_R_list.induct)
apply(case_tac n)
apply(auto dest: in_R_list_split DESTRimpl_rule1 DESTRimpl_rule2 DESTRimpl_rule3 split: option.splits)
done

lemma in_R_list_les: "in_R_list nis ns s \<Longrightarrow> les s s' \<Longrightarrow> in_R_list nis ns s'"
  by(induction rule: in_R_list.induct, auto simp add: les_def)

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

lemma ite_impl_R: "ite_impl ii ti ei s = Some (r, s')
       \<Longrightarrow> in_R_list [ii, ti, ei] [i, t, e] s
       \<Longrightarrow> les s s' \<and> (r, ifex_ite i t e) \<in> R s'"
proof(induction i t e arbitrary: s s' ii ti ei r rule: ifex_ite_induct)
case ("3" i t e a)
  note IFCase = "3"
  from in_R_list_lt[OF this(4)] this(2) have 0: "lowest_tops_impl [ii, ti, ei] s = Some a" by simp
  from IFCase(3) obtain tb st
    where tb_def: "ite_impl (restrict_top_impl ii a True s) (restrict_top_impl ti a True s)
                       (restrict_top_impl ei a True s) s = Some (tb, st)"
    apply(subst (asm) (2) ite_impl.simps, subst (asm) 0, 
          simp only: option.case Let_def Option.bind_eq_Some_conv)
    by fast
  from IFCase(3) obtain eb se
    where eb_def: "ite_impl (restrict_top_impl ii a False s) (restrict_top_impl ti a False s)
                       (restrict_top_impl ei a False s) st = Some (eb, se)"
    apply(subst (asm) (2) ite_impl.simps, subst (asm) 0, 
          auto simp del: restrict_top_impl.simps simp add: Option.bind_eq_Some_conv)
    using tb_def by force
  from IFCase(4) have 2:
    "in_R_list 
     [restrict_top_impl ii a True s, restrict_top_impl ti a True s, restrict_top_impl ei a True s]
     [restrict_top i a True, restrict_top t a True, restrict_top e a True]
     s"
    "in_R_list 
     [restrict_top_impl ii a False s, restrict_top_impl ti a False s, restrict_top_impl ei a False s]
     [restrict_top i a False, restrict_top t a False, restrict_top e a False]
     s"
    by (auto simp del: restrict_top_impl.simps)
  from IFCase(1)[OF tb_def this(1)] have
    3: "(tb,
         ifex_ite (restrict_top i a True) (restrict_top t a True) (restrict_top e a True)) \<in> R st"
       "les s st" by blast+
  note 41 =  in_R_list_les[OF 2(2), of st]
  from IFCase(1)[OF eb_def 41] 3
  have 4: "(eb,
        ifex_ite (restrict_top i a False) (restrict_top t a False) (restrict_top e a False)) \<in> R se"
       "les st se" by auto
  from IFCase(3) have 5: "ite_impl ii ti ei s = Some (IFimpl a tb eb se)"
    apply(subst (asm) ite_impl.simps, subst (asm) 0,
          auto simp del: restrict_top_impl.simps simp add: Option.bind_eq_Some_conv)
    using tb_def eb_def by auto
  from 3 4(2) les_def[of st se]
    have 8: "(tb, 
           ifex_ite (restrict_top i a True) (restrict_top t a True) (restrict_top e a True)) \<in> R se"
    by blast
  from IFimpl_mono[OF this 4(1), of a r s'] 5 IFCase(3) have "les se s'" by fastforce
  from this 3 4(2) les_trans have goal11: "les s s'" by blast
  from IFCase(2)
    have 7:
    "ifex_ite i t e =
     IFC a (ifex_ite (restrict_top i a True) (restrict_top t a True) (restrict_top e a True))
      (ifex_ite (restrict_top i a False) (restrict_top t a False) (restrict_top e a False))"
    by simp
  from 5 IFCase(3) have "IFimpl a tb eb se = (r, s')" by force
  from goal11 IFimpl_rule[OF 8 4(1) this] 7 show ?case
  by(auto split: ifc_split)
next
case("1" i t e) note TrueIFCase = "1"
  from in_R_list_lt[OF this(4)] this(1,2,4) DESTRimpl_rule1
    have 0: "lowest_tops_impl [ii, ti, ei] s = None"
            "DESTRimpl ii s = TD" by simp_all
  from this(1,2) TrueIFCase(3) have 1: "r = ti" apply(subst (asm) ite_impl.simps) by auto
  from 0(1,2) TrueIFCase(3) have    2: "s = s'" apply(subst (asm) ite_impl.simps) by auto
  from TrueIFCase(1,2) have 3: "ifex_ite i t e = t" by simp
  from TrueIFCase(4) have 4: "(ti,t) \<in> R s" by simp
  from les_refl 2 1 3 4 show ?case by presburger
next
case("2" i t e) note FalseIFCase = "2"
  from in_R_list_lt[OF this(4)] this(1,2,4) DESTRimpl_rule2
    have 0: "lowest_tops_impl [ii, ti, ei] s = None"
            "DESTRimpl ii s = FD" by simp_all
  from this(1,2) FalseIFCase(3) have 1: "r = ei" by(auto simp add: ite_impl.simps)
  from 0(1,2) FalseIFCase(3) have    2: "s = s'" by(auto simp add: ite_impl.simps)
  from FalseIFCase(1,2) have 3: "ifex_ite i t e = e" by simp
  from FalseIFCase(4) have 4: "(ei,e) \<in> R s" by simp
  show ?case unfolding 2[symmetric] 1 3 by(rule, rule les_refl, rule 4)
qed

partial_function(option) val_impl     :: "'ni \<Rightarrow> 's \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool option" 
where
"eval_impl e s ass = (case (DESTRimpl e s) of
	TD \<Rightarrow> Some True |
	FD \<Rightarrow> Some False |
	(IFD v t e) \<Rightarrow> eval_impl (if ass v then t else e) s ass)"

lemma "(ni,n) \<in> R s \<Longrightarrow> Some (val_ifex n ass) = val_impl ni s ass"
proof(induction n arbitrary: ni, ((drule DESTRimpl_rule1 | drule DESTRimpl_rule2), simp add: val_impl.simps)+, drule DESTRimpl_rule3, clarify)
	case goal1
	note mIH = goal1(1)[OF goal1(4)] goal1(2)[OF goal1(5)]
	show ?case by(subst val_impl.simps) (simp add: mIH goal1(3))
qed

end
end
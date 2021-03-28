theory MkIfex
  imports BDT
begin

(* bf_vars can be rather useless, it's not a good definition *)
lemma "bf_vars (\<lambda>assmt. finite {x. assmt x}) = {}"
proof -
  have ceq: "Collect (x(y:= True)) = insert y (Collect x)" "Collect (x(y:= False)) = Set.remove y (Collect x)" for x y
    by (auto ; metis)+
  show ?thesis
    unfolding bf_vars_def Collect_empty_eq bf_restrict_def not_ex not_not ceq  remove_def
    by simp
qed

fun mk_ifex :: "'a boolfunc \<Rightarrow> 'a list \<Rightarrow> 'a ifex" where
"mk_ifex f [] = (if f undefined then Trueif else Falseif)" |
"mk_ifex f (v#vs) = IF v (mk_ifex (bf_restrict v True f) vs) (mk_ifex (bf_restrict v False f) vs)"

definition "reads_inside_set f x \<equiv> (\<forall>assmt1 assmt2. (\<forall>p. p \<in> x \<longrightarrow> assmt1 p = assmt2 p) \<longrightarrow> f assmt1 = f assmt2)"

lemma reads_inside_set_subset: "reads_inside_set f a \<Longrightarrow> a \<subseteq> b \<Longrightarrow> reads_inside_set f b"
  unfolding reads_inside_set_def by blast

lemma reads_inside_set_bf_vars: "reads_inside_set f x \<Longrightarrow> bf_vars f \<subseteq> x"
  unfolding bf_vars_def reads_inside_set_def bf_restrict_def
  apply(rule subsetI)
  apply(unfold mem_Collect_eq)
  apply(erule exE)
  apply(metis fun_upd_apply) (* meh *)
  done


lemma const_funcs_finite: "reads_inside_set bf_True {}" "reads_inside_set bf_False {}" unfolding reads_inside_set_def by blast+
lemma lit_finite: "reads_inside_set (bf_lit x) {x}" unfolding bf_lit_def reads_inside_set_def by blast
lemma combine_funcs_finite:
  assumes "reads_inside_set f1 r1" "reads_inside_set f2 r2" "reads_inside_set f3 r3"
  shows "reads_inside_set ((bf_ite f1 f2 f3) :: 'a boolfunc) (r1 \<union> r2 \<union> r3)"
proof -
  define run where "run \<equiv> \<lambda>f :: 'a boolfunc. reads_inside_set f (r1 \<union> r2 \<union> r3)"
  have "run f1" "run f2" "run f3"
    by(unfold run_def; fastforce intro: assms reads_inside_set_subset)+
  thus ?thesis unfolding bf_ite_def run_def reads_inside_set_def by metis
qed

lemma reads_inside_set_restrict: "reads_inside_set f s \<Longrightarrow> reads_inside_set (bf_restrict i v f) (Set.remove i s)"
  unfolding reads_inside_set_def bf_restrict_def by force
text\<open>The opposite direction does not hold - restricting a function on one variable may cause it to stop reading many more variables.\<close>

lemma reads_none: "reads_inside_set f {} \<Longrightarrow> f = bf_True \<or> f = bf_False"
  unfolding reads_inside_set_def by fast (* wow *)

theorem mk_ifex_correct: "reads_inside_set f (set vs) \<Longrightarrow> val_ifex (mk_ifex f vs) assmt \<longleftrightarrow> f assmt"
proof(induction vs arbitrary: f assmt)
  case Nil
  then show ?case using reads_none by auto
next
  case (Cons v vs)
  have "reads_inside_set (bf_restrict v x f) (set vs)" for x
    using reads_inside_set_restrict[OF Cons.prems] reads_inside_set_subset by fastforce
  from Cons.IH[OF this] show ?case 
    unfolding mk_ifex.simps val_ifex.simps bf_restrict_def
    by (simp add: fun_upd_idem)
qed

fun clean_ifex :: "('a :: linorder) ifex \<Rightarrow> 'a ifex" where
"clean_ifex Trueif = Trueif" |
"clean_ifex Falseif = Falseif" |
"clean_ifex (IF i t e) = ifex_ite (IF i Trueif Falseif) (clean_ifex t) (clean_ifex e)"

lemma clean_ifex: "ro_ifex (clean_ifex e) \<and> val_ifex (clean_ifex e) = val_ifex e"
proof(induction e)
  case (IF i t e)
  have m: "ifex_ordered (IF i Trueif Falseif)" "ifex_minimal (IF i Trueif Falseif)" by simp_all
  have "ro_ifex (clean_ifex (IF i t e))" by
    (unfold clean_ifex.simps; intro conjI order_ifex_ite_invar minimal_ifex_ite_invar)
    (simp_all add: IF m)
  moreover have "val_ifex (clean_ifex (IF i t e)) = val_ifex (IF i t e)"
    by(subst clean_ifex.simps; subst val_ifex_ite_subst) (auto intro: val_ifex_ite_subst simp add: IF m bf_ite_def)
  ultimately show ?case ..
qed simp_all

end
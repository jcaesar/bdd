theory BDT
imports Boolean_Expression_Checkers BoolFunc "~~/src/HOL/Library/Monad_Syntax"
begin

(* datatype 'a ifex = Trueif | Falseif | IF 'a "'a ifex" "'a ifex" *)
(* type_synonym boolfunc2 = "(nat \<Rightarrow> bool) \<Rightarrow> bool" *)


fun ifex_vars :: "('a :: linorder) ifex \<Rightarrow> 'a list" where
  "ifex_vars (IF v t e) =  v # ifex_vars t @ ifex_vars e" |
  "ifex_vars Trueif = []" |
  "ifex_vars Falseif = []"

fun ifex_ordered :: "('a::linorder) ifex \<Rightarrow> bool" where
  "ifex_ordered (IF v t e) = ((\<forall>tv \<in> set (ifex_vars t @ ifex_vars e). v < tv)
                       \<and> ifex_ordered t \<and> ifex_ordered e)" |
  "ifex_ordered Trueif = True" |
  "ifex_ordered Falseif = True"

definition ifex_bf2_rel where
  "ifex_bf2_rel = {(a,b). (\<forall>ass. a ass \<longleftrightarrow> val_ifex b ass) \<and> ifex_ordered b}"

lemma nonempty_if_var_set: "ifex_vars (IF v t e) \<noteq> []" by auto

fun restrict where
  "restrict (IF v t e) var val = (let rt = restrict t var val; re = restrict e var val in
                   (if v = var then (if val then rt else re) else (IF v rt re)))" |
  "restrict i _ _ = i"

declare Let_def[simp]

lemma not_element_restrict: "var \<notin> set (ifex_vars (restrict b var val))"
  by (induction b) auto

lemma restrict_assignment: "val_ifex b (ass(var := val)) \<longleftrightarrow> val_ifex (restrict b var val) ass"
  by (induction b) auto

lemma restrict_variables_subset: "set (ifex_vars (restrict b var val)) \<subseteq> set (ifex_vars b)"
  by (induction b) auto

lemma restrict_ifex_ordered_invar: "ifex_ordered b \<Longrightarrow> ifex_ordered (restrict b var val)"
  using restrict_variables_subset by (induction b) (fastforce)+

lemma restrict_val_invar: "\<forall>ass. a ass = val_ifex b ass \<Longrightarrow> 
      (bf2_restrict var val a) ass = val_ifex (restrict b var val) ass"
  unfolding bf2_restrict_def using restrict_assignment by simp

lemma restrict_ifex_bf2_rel:
"(a, b) \<in> ifex_bf2_rel \<Longrightarrow> (bf2_restrict var val a, restrict b var val) \<in> ifex_bf2_rel"
  unfolding ifex_bf2_rel_def using restrict_ifex_ordered_invar restrict_val_invar
  by (clarsimp simp add: bf2_restrict_def restrict_assignment)

lemma restrict_untouched_id: "x \<notin> set (ifex_vars t) \<Longrightarrow> restrict t x val = t" (* umkehrung gilt auch\<dots> *)
proof(induction t)
	case (IF v t e)
	from IF.prems have "x \<notin> set (ifex_vars t)" "x \<notin> set (ifex_vars e)" by simp_all
	note mIH = IF.IH(1)[OF this(1)] IF.IH(2)[OF this(2)]
	from IF.prems have "x \<noteq> v" by simp
	thus ?case unfolding restrict.simps Let_def mIH  by simp
qed simp_all

fun ifex_top_var :: "'a ifex \<Rightarrow> 'a option" where
  "ifex_top_var (IF v t e) = Some v" |
  "ifex_top_var _ = None"

fun restrict_top :: "('a :: linorder) ifex \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'a ifex" where
  "restrict_top (IF v t e) var val = (if v = var then (if val then t else e) else (IF v t e))" |
  "restrict_top i _ _ = i"

(* dunno if the following four are useful for something\<dots> *)
lemma restrict_top_id: "ifex_ordered e \<Longrightarrow> ifex_top_var e = Some v \<Longrightarrow> v' < v \<Longrightarrow> restrict_top e v' val = e"
	by(induction e) auto
lemma restrict_id: "ifex_ordered e \<Longrightarrow> ifex_top_var e = Some v \<Longrightarrow> v' < v \<Longrightarrow> restrict e v' val = e"
	apply(induction e arbitrary: v)
	  apply simp_all[2]
	apply(case_tac e1, case_tac[!] e2)
	        apply simp_all[2]
	      apply fastforce
	     apply simp_all[2]
	   apply fastforce
	  apply fastforce
	 apply fastforce
	apply force (* meh *)
done
lemma restrict_top_IF_id: "ifex_ordered (IF v t e) \<Longrightarrow> v' < v \<Longrightarrow> restrict_top (IF v t e) v' val = (IF v t e)"
	using restrict_top_id by auto
lemma restrict_IF_id: assumes o: "ifex_ordered (IF v t e)" assumes le: "v' < v"
	shows "restrict (IF v t e) v' val = (IF v t e)"
	using restrict_id[OF o, unfolded ifex_top_var.simps, OF refl le, of val] .

lemma restrict_top_eq: "ifex_ordered (IF v t e) \<Longrightarrow> restrict (IF v t e) v val = restrict_top (IF v t e) v val"
	using restrict_untouched_id by auto

lemma restrict_top_ifex_ordered_invar: "ifex_ordered b \<Longrightarrow> ifex_ordered (restrict_top b var val)"
  by (induction b) simp_all

fun lowest_tops :: "('a :: linorder) ifex list \<Rightarrow> 'a option" where
"lowest_tops [] = None" |
"lowest_tops ((IF v _ _)#r) = Some (case lowest_tops r of Some u \<Rightarrow> (min u v) | None \<Rightarrow> v)" |
"lowest_tops (_#r) = lowest_tops r"

lemma lowest_tops_NoneD: "lowest_tops k = None \<Longrightarrow> (\<not>(\<exists>v t e. ((IF v t e) \<in> set k)))"
by(induction k rule: lowest_tops.induct) simp_all
lemma lowest_tops_in: "lowest_tops k = Some l \<Longrightarrow> l \<in> set (concat (map ifex_vars k))"
  by(induction k rule: lowest_tops.induct) (simp_all split: option.splits if_splits add: min_def)

function ifex_ite :: "'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> ('a :: linorder) ifex" where
  "ifex_ite i t e = (case lowest_tops [i, t, e] of Some x \<Rightarrow> 
                         (IF x (ifex_ite (restrict_top i x True) (restrict_top t x True) (restrict_top e x True))
                               (ifex_ite (restrict_top i x False) (restrict_top t x False) (restrict_top e x False)))
                     | None \<Rightarrow> (case i of Trueif \<Rightarrow> t | Falseif \<Rightarrow> e))"
by pat_completeness auto

lemma restrict_size_le: "size (restrict_top k var val) \<le> size k"
  by (induction k, auto)

lemma restrict_size_less: "ifex_top_var k = Some var \<Longrightarrow> size (restrict_top k var val) < size k"
 by (induction k, auto)


(* I'm commander Shepard and this is my favourite proof in this repository *)
(* Heyy, this is Kelly. I optimized your proof for you. I hope you still like it. *)
lemma lowest_tops_cases: "lowest_tops [i, t, e] = Some var \<Longrightarrow>
       ifex_top_var i = Some var \<or> ifex_top_var t = Some var \<or> ifex_top_var e = Some var"
apply(cases i, case_tac[!] t, case_tac[!] e)
apply(auto simp add: min_def)
done

lemma termlemma2: "lowest_tops [i, t, e] = Some xa \<Longrightarrow>
  (size (restrict_top i xa val) + size (restrict_top t xa val) + size (restrict_top e xa val)) <
  (size i + size t + size e)"
  using restrict_size_le[of i xa val] restrict_size_le[of t xa val]  restrict_size_le[of e xa val] 
by (auto dest!: lowest_tops_cases restrict_size_less[of _ _ val])

lemma termlemma: "lowest_tops [i, t, e] = Some xa \<Longrightarrow>
       (case (restrict_top i xa val, restrict_top t xa val, restrict_top e xa val) of 
             (i, t, e) \<Rightarrow> size i + size t + size e) <
       (case (i, t, e) of (i, t, e) \<Rightarrow> size i + size t + size e)"
using termlemma2 by fast

termination ifex_ite
  by (relation "measure (\<lambda>(i,t,e). size i + size t + size e)", rule wf_measure, unfold in_measure) 
     (simp_all only: termlemma)


definition "const x _ = x" (* Mehr Haskell wagen *)
lemma rel_true_false: "(a, Trueif) \<in> ifex_bf2_rel \<Longrightarrow> a = const True" "(a, Falseif) \<in> ifex_bf2_rel \<Longrightarrow> a = const False"
	unfolding fun_eq_iff const_def
	unfolding ifex_bf2_rel_def 
	by simp_all
lemma rel_if: "(a, IF v t e) \<in> ifex_bf2_rel \<Longrightarrow> (ta, t) \<in> ifex_bf2_rel \<Longrightarrow> (ea, e) \<in> ifex_bf2_rel \<Longrightarrow> a = (\<lambda>as. if as v then ta as else ea as)"
	unfolding fun_eq_iff const_def
	unfolding ifex_bf2_rel_def 
	by simp_all
lemma "as v \<Longrightarrow> (a, (IF v t e)) \<in> ifex_bf2_rel \<Longrightarrow> (bf2_restrict v True a, t) \<in> ifex_bf2_rel"
unfolding in_rel_def[symmetric]
unfolding ifex_bf2_rel_def
unfolding in_rel_Collect_split_eq
unfolding val_ifex.simps
unfolding ifex_ordered.simps
unfolding bf2_restrict_def
oops
lemma ifex_bf2_construct: "(ta, tb) \<in> ifex_bf2_rel \<Longrightarrow> (ea, eb) \<in> ifex_bf2_rel \<Longrightarrow> ifex_ordered (IF x tb eb) \<Longrightarrow> (\<lambda>as. if as x then ta as else ea as, IF x tb eb) \<in> ifex_bf2_rel"
	unfolding fun_eq_iff const_def
	unfolding ifex_bf2_rel_def
	by simp
	
lemma ifex_ordered_implied: "(a, b) \<in> ifex_bf2_rel \<Longrightarrow> ifex_ordered b" unfolding ifex_bf2_rel_def by simp

lemma single_valued_rel: "single_valued (ifex_bf2_rel\<inverse>)"
	unfolding single_valued_def
	unfolding ifex_bf2_rel_def
	unfolding converse_unfold
	unfolding in_rel_def[symmetric]  in_rel_Collect_split_eq
	by blast


lemma ifex_ite_induct: "
  (\<And>i t e. lowest_tops [i, t, e] = None \<Longrightarrow> i = Trueif \<Longrightarrow> sentence i t e) \<Longrightarrow>
  (\<And>i t e. lowest_tops [i, t, e] = None \<Longrightarrow> i = Falseif \<Longrightarrow> sentence i t e) \<Longrightarrow>
  (\<And>i t e a. (\<And>val. sentence (restrict_top i a val) (restrict_top t a val) (restrict_top e a val)) \<Longrightarrow> 
   lowest_tops [i, t, e] = Some a \<Longrightarrow> sentence i t e) \<Longrightarrow> sentence i t e"
proof(induction i t e rule: ifex_ite.induct)
	case goal1 show ?case
	proof(cases "lowest_tops [i, t, e]")
		case None thus ?thesis by (cases i) (auto intro: goal1)
	next
		case (Some a) show ?thesis
			apply(rule goal1(5)[OF _ Some]) 
			apply(case_tac val) 
			 apply(simp_all) 
			 apply(rule goal1(1)[OF Some]) 
			   apply(blast intro: goal1(5) dest: goal1(3,4))+
			apply(rule goal1(2)[OF Some]) 
			   apply(blast intro: goal1(5) dest: goal1(3,4))+
		    done
  qed
qed

lemma order_ifex_ite_invar: "ifex_ordered i \<Longrightarrow> ifex_ordered t \<Longrightarrow> ifex_ordered e \<Longrightarrow> ifex_ordered (ifex_ite i t e)"
	apply(induction i t e rule: ifex_ite_induct)
	apply simp
	apply simp
	proof -
		case goal1
		note l = restrict_top_ifex_ordered_invar
		note l[OF goal1(3)] l[OF goal1(4)] l[OF goal1(5)]
		note goal1(1)[OF this]
		thus ?case apply(subst ifex_ite.simps) unfolding goal1(2) apply(simp del: ifex_ite.simps) apply rule
oops

end

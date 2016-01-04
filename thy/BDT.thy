theory BDT
imports Boolean_Expression_Checkers BoolFunc "~~/src/HOL/Library/Monad_Syntax"
begin

(* datatype 'a ifex = Trueif | Falseif | IF 'a "'a ifex" "'a ifex" *)
(* type_synonym boolfunc2 = "(nat \<Rightarrow> bool) \<Rightarrow> bool" *)


fun ifex_vars :: "('a :: linorder) ifex \<Rightarrow> 'a list" where
  "ifex_vars (IF v t e) =  v # ifex_vars t @ ifex_vars e" |
  "ifex_vars Trueif = []" |
  "ifex_vars Falseif = []"

abbreviation "ifex_var_set a \<equiv> set (ifex_vars a)"

fun ifex_ordered :: "('a::linorder) ifex \<Rightarrow> bool" where
  "ifex_ordered (IF v t e) = ((\<forall>tv \<in> (ifex_var_set t \<union> ifex_var_set e). v < tv)
                       \<and> ifex_ordered t \<and> ifex_ordered e)" |
  "ifex_ordered Trueif = True" |
  "ifex_ordered Falseif = True"

fun ifex_minimal :: "('a::linorder) ifex \<Rightarrow> bool" where
  "ifex_minimal (IF v t e) \<longleftrightarrow> t \<noteq> e \<and> ifex_minimal t \<and> ifex_minimal e" |
  "ifex_minimal Trueif = True" |
  "ifex_minimal Falseif = True"

abbreviation ro_ifex where "ro_ifex t \<equiv> ifex_ordered t \<and> ifex_minimal t"

definition bf_ifex_rel where
  "bf_ifex_rel = {(a,b). (\<forall>ass. a ass \<longleftrightarrow> val_ifex b ass) \<and> ro_ifex b}"

lemma ifex_var_noinfluence: "x \<notin> ifex_var_set b \<Longrightarrow> val_ifex b (ass(x:=val)) = val_ifex b ass"
  by (induction b, auto)  

lemma roifex_var_not_in_subtree:
  assumes "ro_ifex b" and "b = IF v t e" 
  shows "v \<notin> ifex_var_set t" and "v \<notin> ifex_var_set e"
using assms by (induction, auto)

lemma roifex_var_no_influence_subtree: 
  assumes "ro_ifex b" and "b = IF v t e"
  shows "val_ifex t (ass(v:=val)) = val_ifex t ass" 
        "val_ifex e (ass(v:=val)) = val_ifex e ass"
  using assms by (auto intro!: ifex_var_noinfluence dest: roifex_var_not_in_subtree)

lemma roifex_set_var_subtree: 
  assumes "ro_ifex b" and "b = IF v t e"
  shows "val_ifex b (ass(v:=True)) = val_ifex t ass" 
        "val_ifex b (ass(v:=False)) = val_ifex e ass"
  using assms by (auto intro!: ifex_var_noinfluence dest: roifex_var_not_in_subtree)

lemma roifex_Trueif_unique: "ro_ifex b \<Longrightarrow> \<forall>ass. val_ifex b ass \<Longrightarrow> b = Trueif"
proof(induction b)
  case (IF v b1 b2) with roifex_set_var_subtree[OF IF(3), of v b1 b2] show ?case by simp
qed(auto)

lemma roifex_Falseif_unique: "ro_ifex b \<Longrightarrow> \<forall>ass. \<not> val_ifex b ass \<Longrightarrow> b = Falseif"
proof(induction b)
  case (IF v b1 b2) with roifex_set_var_subtree[OF IF(3), of v b1 b2] show ?case by fastforce
qed(auto)

lemma "(f, b) \<in> bf_ifex_rel \<Longrightarrow>  b = Trueif \<longleftrightarrow> f = (\<lambda>_. True)"
  unfolding bf_ifex_rel_def using roifex_Trueif_unique by auto

lemma "(f, b) \<in> bf_ifex_rel \<Longrightarrow>  b = Falseif \<longleftrightarrow> f = (\<lambda>_. False)"
  unfolding bf_ifex_rel_def using roifex_Falseif_unique by auto

lemma ro_ifex_true_assign: assumes "ro_ifex b" "b = IF v b1 b2" shows "\<exists>ass. val_ifex b ass"
using assms proof(induction b arbitrary: v b1 b2)
  case(IF v' b1' b2') note IFind = IF show ?case
    proof(cases b1')
      case Trueif thus ?thesis by auto
    next
      case Falseif with IF(2) IF(3) show ?thesis 
        proof(cases b2')
          case (IF v2 b21 b22) 
            from IFind(2)[OF _ this] IFind(3) obtain a where a_def: "val_ifex b2' a" by auto
           note this = roifex_set_var_subtree(2)[OF IFind(3), of v' b1' b2' a]
           from a_def this show ?thesis by blast
        qed(auto)
    next
      case (IF v1 b11 b12) 
        from IFind(1)[OF _ this] roifex_set_var_subtree(1)[OF IFind(3), of v' b1' b2'] IFind(3)
          show ?thesis by fastforce
    qed
qed (auto)

lemma ro_ifex_false_assign: assumes "ro_ifex b" "b = IF v b1 b2" shows "\<exists>ass. \<not> val_ifex b ass"
using assms proof(induction b arbitrary: v b1 b2)
  case(IF v' b1' b2') note IFind = IF show ?case
    proof(cases b1')
      case Falseif thus ?thesis by auto
    next
      case Trueif with IF(2) IF(3) show ?thesis 
        proof(cases b2')
          case (IF v2 b21 b22) 
            from IFind(2)[OF _ this] IFind(3) obtain a where a_def: "\<not> val_ifex b2' a" by auto
           note this = roifex_set_var_subtree(2)[OF IFind(3), of v' b1' b2' a]
           from a_def this show ?thesis by blast
        qed(auto)
    next
      case (IF v1 b11 b12) 
        from IFind(1)[OF _ this] roifex_set_var_subtree(1)[OF IFind(3), of v' b1' b2'] IFind(3)
          show ?thesis by fastforce
    qed
qed (auto)

lemma ifex_ordered_not_part: "ifex_ordered  b \<Longrightarrow> b = IF v b1 b2 \<Longrightarrow> w < v \<Longrightarrow> w \<notin> ifex_var_set b"
	using less_asym by fastforce

lemma ro_ifex_unique: "ro_ifex x \<Longrightarrow> ro_ifex y \<Longrightarrow> \<forall>ass. val_ifex x ass = val_ifex y ass \<Longrightarrow> x = y"
 proof(induction x arbitrary: y)
  case (IF xv xb1 xb2) note IFind = IF from this(3,4,5) show ?case
    proof(induction y)
      case (IF yv yb1 yb2)
  thm IF IFind(3,4,5) IFind(1)[of yb1] IFind(2)[of yb2]
  obtain x where x_def: "x = IF xv xb1 xb2" by simp
  obtain y' where y'_def: "y' = IF yv yb1 yb2" by simp
  from y'_def x_def IFind(3,4) IF have 0: "ro_ifex xb1" "ro_ifex xb2" "ro_ifex yb1" "ro_ifex yb2" 
                                          "ro_ifex x" "ro_ifex y'" by auto
  from IF IFind(5) x_def y'_def have 1: "\<forall>ass. val_ifex x ass = val_ifex y' ass" by simp
  show ?case proof(cases "xv = yv")
    note roifex_set_var_subtree(1)[OF 0(5) x_def, symmetric]
    case True
      from roifex_set_var_subtree(1)[OF 0(5) x_def]
           roifex_set_var_subtree(1)[OF 0(6) y'_def] 1 True IFind(1)[OF 0(1) 0(3)]
           have 3: "xb1 = yb1" by blast
      from roifex_set_var_subtree(2)[OF 0(5) x_def]
           roifex_set_var_subtree(2)[OF 0(6) y'_def] 1 True IFind(2)[OF 0(2) 0(4)]
           have 4: "xb2 = yb2" by blast
      from True 3 4 IF show ?thesis by simp
    next
    case False note uneq = False show ?thesis
      proof(cases "xv < yv")
        case True
          from ifex_ordered_not_part[OF _ y'_def True] ifex_var_noinfluence[of xv y' _ "True"]
               0(6) roifex_set_var_subtree(1)[OF 0(5) x_def] 1
             have 5: "\<And>ass. val_ifex xb1 ass = val_ifex x ass" by blast
          from 0(5) ifex_var_noinfluence[of xv xb1 _ "False"] 
                    ifex_var_noinfluence[of xv xb2 _ "False"] 
               x_def
            have "\<And>ass. val_ifex xb1 (ass(xv := False)) = val_ifex xb1 ass"
                 "\<And>ass. val_ifex xb2 (ass(xv := False)) = val_ifex xb2 ass" by auto
          from 5 this roifex_set_var_subtree(2)[OF 0(5) x_def]
            have "\<And>ass. val_ifex xb1 ass = val_ifex xb2 ass" by presburger
          from IFind(1)[OF 0(1) 0(2)] this IFind(3) have "False" by auto
          from this show ?thesis ..
      next
        case False
          from this uneq have 6: "yv < xv" by auto
          from ifex_ordered_not_part[OF _ x_def this]
                     ifex_var_noinfluence[of yv x] 0(5)
             have  "\<And>ass val. val_ifex x (ass(yv := val)) = val_ifex x ass" 
                   "\<And>ass val. val_ifex x (ass(yv := val)) =  val_ifex x ass" by auto
          from this roifex_set_var_subtree[OF 0(5) x_def]
            have "\<And>ass val. val_ifex x (ass(xv := True, yv := val)) = val_ifex xb1 ass"
                 "\<And>ass val. val_ifex x (ass(xv := False, yv := val)) = val_ifex xb2 ass" by blast+
          from ifex_ordered_not_part[OF _ x_def 6] 0(5) ifex_var_noinfluence[of yv x] 1
               roifex_set_var_subtree[OF 0(6) y'_def]
            have "\<And>ass val. val_ifex x ass = val_ifex yb1 ass"
                 "\<And>ass val. val_ifex x ass = val_ifex yb2 ass" by blast+
          from this IF(1,2) x_def 0(5) y'_def 0(6) have "x = yb1" "x = yb2" by fastforce+
          from this have "yb1 = yb2" by auto
          from 0(6) y'_def this have "False" by auto
          thus ?thesis ..
      qed
  qed
qed (fastforce intro: roifex_Falseif_unique roifex_Trueif_unique)+
qed (fastforce intro: roifex_Falseif_unique[symmetric] roifex_Trueif_unique[symmetric])+

lemma "single_valued bf_ifex_rel" "single_valued (bf_ifex_rel\<inverse>)"
  unfolding single_valued_def bf_ifex_rel_def using ro_ifex_unique by auto

lemma nonempty_if_var_set: "ifex_vars (IF v t e) \<noteq> []" by auto

fun restrict where
  "restrict (IF v t e) var val = (let rt = restrict t var val; re = restrict e var val in
                   (if v = var then (if val then rt else re) else (IF v rt re)))" |
  "restrict i _ _ = i"

declare Let_def[simp]

lemma not_element_restrict: "var \<notin> ifex_var_set (restrict b var val)"
  by (induction b) auto

lemma restrict_assignment: "val_ifex b (ass(var := val)) \<longleftrightarrow> val_ifex (restrict b var val) ass"
  by (induction b) auto

lemma restrict_variables_subset: "ifex_var_set (restrict b var val) \<subseteq> ifex_var_set b"
  by (induction b) auto

lemma restrict_ifex_ordered_invar: "ifex_ordered b \<Longrightarrow> ifex_ordered (restrict b var val)"
  using restrict_variables_subset by (induction b) (fastforce)+

lemma restrict_val_invar: "\<forall>ass. a ass = val_ifex b ass \<Longrightarrow> 
      (bf_restrict var val a) ass = val_ifex (restrict b var val) ass"
  unfolding bf_restrict_def using restrict_assignment by simp

lemma restrict_untouched_id: "x \<notin> ifex_var_set t \<Longrightarrow> restrict t x val = t" (* umkehrung gilt auch\<dots> *)
proof(induction t)
	case (IF v t e)
	from IF.prems have "x \<notin> ifex_var_set t" "x \<notin> ifex_var_set e" by simp_all
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

definition "IFC v t e \<equiv> (if t = e then t else IF v t e)" 


function ifex_ite :: "'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> ('a :: linorder) ifex" where
  "ifex_ite i t e = (case lowest_tops [i, t, e] of Some x \<Rightarrow> 
                         (IFC x (ifex_ite (restrict_top i x True) (restrict_top t x True) (restrict_top e x True))
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

lemma lowest_tops_lowest: "lowest_tops es = Some a \<Longrightarrow> e \<in> set es \<Longrightarrow> ifex_ordered e \<Longrightarrow> v \<in> ifex_var_set e \<Longrightarrow> a \<le> v"
apply((induction arbitrary: a rule: lowest_tops.induct))
apply(case_tac[!] e, simp_all add: min_def Ball_def less_imp_le split: if_splits option.splits)
apply (meson less_imp_le lowest_tops_NoneD order_refl)
apply fastforce+
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
lemma rel_true_false: "(a, Trueif) \<in> bf_ifex_rel \<Longrightarrow> a = const True" "(a, Falseif) \<in> bf_ifex_rel \<Longrightarrow> a = const False"
	unfolding fun_eq_iff const_def
	unfolding bf_ifex_rel_def 
	by simp_all
lemma rel_if: "(a, IF v t e) \<in> bf_ifex_rel \<Longrightarrow> (ta, t) \<in> bf_ifex_rel \<Longrightarrow> (ea, e) \<in> bf_ifex_rel \<Longrightarrow> a = (\<lambda>as. if as v then ta as else ea as)"
	unfolding fun_eq_iff const_def
	unfolding bf_ifex_rel_def 
	by simp_all
lemma "as v \<Longrightarrow> (a, (IF v t e)) \<in> bf_ifex_rel \<Longrightarrow> (bf2_restrict v True a, t) \<in> bf_ifex_rel"
unfolding in_rel_def[symmetric]
unfolding bf_ifex_rel_def
unfolding in_rel_Collect_split_eq
unfolding val_ifex.simps
unfolding ifex_ordered.simps
unfolding bf_restrict_def
oops
	
lemma ifex_ordered_implied: "(a, b) \<in> bf_ifex_rel \<Longrightarrow> ifex_ordered b" unfolding bf_ifex_rel_def by simp
lemma ifex_minimal_implied: "(a, b) \<in> bf_ifex_rel \<Longrightarrow> ifex_minimal b" unfolding bf_ifex_rel_def by simp

lemma single_valued_rel: "single_valued (bf_ifex_rel\<inverse>)"
	unfolding single_valued_def
	unfolding bf_ifex_rel_def
	unfolding converse_unfold
	unfolding in_rel_def[symmetric]  in_rel_Collect_split_eq
	by blast


lemma ifex_ite_induct2: "
  (\<And>i t e. lowest_tops [i, t, e] = None \<Longrightarrow> i = Trueif \<Longrightarrow> sentence i t e) \<Longrightarrow>
  (\<And>i t e. lowest_tops [i, t, e] = None \<Longrightarrow> i = Falseif \<Longrightarrow> sentence i t e) \<Longrightarrow>
  (\<And>i t e a. sentence (restrict_top i a True) (restrict_top t a True) (restrict_top e a True) \<Longrightarrow>
             sentence (restrict_top i a False) (restrict_top t a False) (restrict_top e a False) \<Longrightarrow>
   lowest_tops [i, t, e] = Some a \<Longrightarrow> sentence i t e) \<Longrightarrow> sentence i t e"
proof(induction i t e rule: ifex_ite.induct)
	case goal1 show ?case
	proof(cases "lowest_tops [i, t, e]")
		case None thus ?thesis by (cases i) (auto intro: goal1)
	next
		case (Some a) thus ?thesis by(auto intro: goal1)
  qed
qed
lemma ifex_ite_induct: "
  (\<And>i t e. lowest_tops [i, t, e] = None \<Longrightarrow> i = Trueif \<Longrightarrow> sentence i t e) \<Longrightarrow>
  (\<And>i t e. lowest_tops [i, t, e] = None \<Longrightarrow> i = Falseif \<Longrightarrow> sentence i t e) \<Longrightarrow>
  (\<And>i t e a. (\<And>val. sentence (restrict_top i a val) (restrict_top t a val) (restrict_top e a val)) \<Longrightarrow> 
   lowest_tops [i, t, e] = Some a \<Longrightarrow> sentence i t e) \<Longrightarrow> sentence i t e"
proof(induction i t e rule: ifex_ite_induct2)
	case goal3
	have "(\<And>val. sentence (restrict_top i a val) (restrict_top t a val) (restrict_top e a val))"
		apply(case_tac val) apply(auto) using goal3(1,2,6) apply(blast intro: goal3(4,5))+ done
	note goal3(6)[OF this goal3(3)] thus ?case .
qed blast+

lemma lowest_restrictor: "lowest_tops e = Some a \<Longrightarrow> (\<And>i. i \<in> set e \<Longrightarrow> ifex_ordered i) \<Longrightarrow> x \<in> \<Union>(set (map (set \<circ> ifex_vars \<circ> (\<lambda>i. restrict_top i a vl)) e)) \<Longrightarrow> a < x"
proof(simp, rule ccontr)
	case goal1
	from goal1(3) obtain xa where xa1: "xa\<in>set e" "x \<in> ifex_var_set (restrict_top xa a vl)" by blast
	obtain v vt ve where xa: "xa = IF v vt ve" apply(cases xa) using xa1 by auto
	have o: "ifex_ordered (IF v vt ve)" using goal1(2) xa1(1) unfolding xa .
	have "x < a" using goal1(4) apply(subgoal_tac "x \<noteq> a", simp) using goal1(3)
	using not_element_restrict[of v "IF v vt ve"] unfolding restrict_top_eq[OF o] 
oops (* forget it *)

lemma restrict_top_subset: "x \<in> ifex_var_set (restrict_top i vr vl) \<Longrightarrow> x \<in> ifex_var_set i"
	by(induction i) (simp_all split: if_splits)

lemma ifex_vars_subset: "x \<in> ifex_var_set (ifex_ite i t e) \<Longrightarrow> (x \<in> ifex_var_set i) \<or> (x \<in> ifex_var_set t) \<or> (x \<in> ifex_var_set e)"
proof(induction rule: ifex_ite_induct2)
	case goal3
	have "x \<in> {x. x = a} \<or> x \<in> (ifex_var_set (ifex_ite (restrict_top i a True) (restrict_top t a True) (restrict_top e a True))) \<or> x \<in> (ifex_var_set (ifex_ite (restrict_top i a False) (restrict_top t a False) (restrict_top e a False)))"
		(*apply(subst ifex_ite.simps) apply(simp only: goal3(2) option.simps ifex_vars.simps set_simps set_append insert_def Un_iff split: option.split) *)
		using goal3 by(simp add: IFC_def split: if_splits) 
	hence "x = a \<or>
		x \<in> (ifex_var_set (restrict_top i a True )) \<or> x \<in> (ifex_var_set (restrict_top t a True )) \<or> x \<in> (ifex_var_set (restrict_top e a True )) \<or>
		x \<in> (ifex_var_set (restrict_top i a False)) \<or> x \<in> (ifex_var_set (restrict_top t a False)) \<or> x \<in> (ifex_var_set (restrict_top e a False))"
	using goal3(1-2) by blast
	thus ?case using restrict_top_subset apply - apply(erule disjE) defer apply blast using  lowest_tops_in[OF goal3(3)] apply(simp only: set_concat set_map set_simps) by blast
qed simp_all

lemma three_ins: "i \<in> set [i, t, e]" "t \<in> set [i, t, e]" "e \<in> set [i, t, e]" by simp_all

lemma hlp3: "lowest_tops (IF v uu uv # r) \<noteq> lowest_tops r \<Longrightarrow> lowest_tops (IF v uu uv # r) = Some v"
	by(simp add: min_def split: option.splits if_splits)
lemma hlp2: "IF vi vt ve \<in> set is
\<Longrightarrow> lowest_tops is = Some a
\<Longrightarrow> a \<le> vi" 
apply(induction "is" arbitrary: vt ve a rule: lowest_tops.induct)
apply(auto simp add: min_def split: if_splits option.splits dest: lowest_tops_NoneD) (* solves all but some of second case *)
apply(meson le_cases order_trans) (* I stared at this for quite a few minutes\<dots> how the\<dots>? *)
done

lemma hlp1: "i \<in> set is \<Longrightarrow> lowest_tops is = Some a \<Longrightarrow> ifex_ordered i \<Longrightarrow> a \<notin> (ifex_var_set (restrict_top i a val))"
proof(rule ccontr, unfold not_not)
	case goal1
	from goal1(4) obtain vi vt ve where vi: "i = IF vi vt ve" by(cases i) simp_all
	with goal1(4) goal1(3) have ne: "vi \<noteq> a" by(simp split: if_splits) blast+
	moreover have "vi \<le> a" using goal1(3,4) proof -
		case goal1
		hence "a \<in> (ifex_var_set vt) \<or> a \<in> (ifex_var_set ve)" using ne by(simp add: vi)
		thus ?case using goal1(1)[unfolded vi ifex_ordered.simps] using less_imp_le by auto
	qed
	moreover have "a \<le> vi" using goal1(1) unfolding vi using goal1(2) hlp2 by metis
	ultimately show False by simp
qed

lemma order_ifex_ite_invar: "ifex_ordered i \<Longrightarrow> ifex_ordered t \<Longrightarrow> ifex_ordered e \<Longrightarrow> ifex_ordered (ifex_ite i t e)"
proof(induction i t e rule: ifex_ite_induct)
	case goal3 note goal1 = goal3
	note l = restrict_top_ifex_ordered_invar
	note l[OF goal1(3)] l[OF goal1(4)] l[OF goal1(5)]
	note mIH = goal1(1)[OF this]
	note blubb = lowest_tops_lowest[OF goal1(2) _ _ restrict_top_subset]
	show ?case using mIH 
	by (subst ifex_ite.simps,
		auto simp del: ifex_ite.simps
			simp add: IFC_def goal1(2) hlp1[OF three_ins(1) goal1(2) goal1(3)] hlp1[OF three_ins(2) goal1(2) goal1(4)] hlp1[OF three_ins(3) goal1(2) goal1(5)] 
			dest: ifex_vars_subset blubb[OF three_ins(1) goal1(3)] blubb[OF three_ins(2) goal1(4)] blubb[OF three_ins(3) goal1(5)] 
			intro!: le_neq_trans) (* lol *)
qed simp_all

lemma ifc_split: "P (IFC v t e) \<longleftrightarrow> ((t = e) \<longrightarrow> P t) \<and> (t \<noteq> e \<longrightarrow> P (IF v t e))"
	unfolding IFC_def by simp

lemma restrict_top_ifex_minimal_invar: "ifex_minimal i \<Longrightarrow> ifex_minimal (restrict_top i a val)"
	by(induction i) simp_all
lemma minimal_ifex_ite_invar: "ifex_minimal i \<Longrightarrow> ifex_minimal t \<Longrightarrow> ifex_minimal e \<Longrightarrow> ifex_minimal (ifex_ite i t e)"
by(induction i t e rule: ifex_ite_induct) (simp_all split: ifc_split option.split add: restrict_top_ifex_minimal_invar)

lemma restrict_top_bf: "i \<in> set is \<Longrightarrow> lowest_tops is = Some vr \<Longrightarrow> 
	ifex_ordered i \<Longrightarrow> (\<And>ass. fi ass = val_ifex i ass) \<Longrightarrow> val_ifex (restrict_top i vr vl) ass = bf_restrict vr vl fi ass"
proof(cases i)
	case goal3
	have rr: "restrict_top i vr vl = restrict i vr vl" 
	proof(cases "x31 = vr")
		case True
		note uf = restrict_top_eq[OF goal3(3)[unfolded goal3(5)], symmetric, unfolded goal3(5)[symmetric], unfolded True]
		thus ?thesis .
	next
		case False
		have 1: "restrict_top i vr vl = i" by (simp add: False goal3(5))
		have "vr < x31" using le_neq_trans[OF hlp2[OF goal3(1)[unfolded goal3(5)] goal3(2)] False[symmetric]] by blast
		with goal3(3,5) have 2: "restrict i vr vl = i" using restrict_IF_id by blast
		show ?thesis unfolding 1 2 ..
	qed
	show ?case unfolding rr by(simp add: goal3(4) restrict_val_invar[symmetric])
qed (simp_all add: bf_restrict_def)

lemma "
	in_rel bf_ifex_rel fi i \<Longrightarrow>
	in_rel bf_ifex_rel ft t \<Longrightarrow>
	in_rel bf_ifex_rel fe e \<Longrightarrow>
	in_rel bf_ifex_rel (bf_ite fi ft fe) (ifex_ite i t e)"
proof -
	case goal1
	from goal1 have o: "ifex_ordered (ifex_ite i t e)" unfolding in_rel_def using ifex_ordered_implied order_ifex_ite_invar by blast
	from goal1 have m: "ifex_minimal (ifex_ite i t e)" unfolding in_rel_def using ifex_minimal_implied minimal_ifex_ite_invar by blast
	have fas: "\<And>ass. fi ass = val_ifex i ass" "\<And>ass. ft ass = val_ifex t ass"  "\<And>ass. fe ass = val_ifex e ass"
		using goal1 unfolding bf_ifex_rel_def by simp_all
	moreover have "ifex_ordered i" "ifex_ordered t" "ifex_ordered e" using goal1 ifex_ordered_implied by simp_all 
	ultimately have "\<And>ass. (bf_ite fi ft fe) ass = val_ifex (ifex_ite i t e) ass"
	proof(induction i t e arbitrary: fi ft fe rule: ifex_ite_induct)
		case goal3
		note mIH = goal3(1)[OF refl refl refl 
			restrict_top_ifex_ordered_invar[OF goal3(6)]
			restrict_top_ifex_ordered_invar[OF goal3(7)]
			restrict_top_ifex_ordered_invar[OF goal3(8)], symmetric]
		note uf1 = restrict_top_bf[OF three_ins(1) goal3(2) goal3(6) goal3(3)]
		           restrict_top_bf[OF three_ins(2) goal3(2) goal3(7) goal3(4)]
		           restrict_top_bf[OF three_ins(3) goal3(2) goal3(8) goal3(5)]
		show ?case by
			(rule trans[OF brace90shannon[where i=a]], unfold bf_ite_def[of "\<lambda>l. l a"])
			(subst ifex_ite.simps, simp only: goal3(1,2,6-8) uf1 mIH  option.simps val_ifex.simps split: ifc_split, 
				simp add: goal3(1) goal3(6) goal3(7) goal3(8) restrict_top_ifex_ordered_invar uf1) 
	qed (subst ifex_ite.simps, simp add: bf_ite_def bf_ifex_rel_def)+
	with o m show ?case unfolding bf_ifex_rel_def by simp
qed

fun ifex_sat where
"ifex_sat Trueif = Some (const False)" |
"ifex_sat Falseif = None" |
"ifex_sat (IF v t e) = 
	(case ifex_sat e of 
		Some a \<Rightarrow> Some (a(v:=False)) |
		None \<Rightarrow> (case ifex_sat t of
			Some a \<Rightarrow> Some (a(v:=True)) |
			None \<Rightarrow> None))
"
lemma ifex_sat_untouched_False: "v \<notin> ifex_var_set i \<Longrightarrow> ifex_sat i = Some a \<Longrightarrow> a v = False"
proof(induction i arbitrary: a)
	case (IF v1 t e)
	have ni: "v \<notin> ifex_var_set t" "v \<notin> ifex_var_set e" using IF.prems(1) by simp_all
	have ne: "v1 \<noteq> v" using IF.prems(1) by force
	show ?case proof(cases "ifex_sat e")
		case (Some as)
		with IF.prems(2) have au: "a = as(v1 := False)" by simp
		moreover from IF.IH(2)[OF ni(2)] have "as v = False" using Some .
		ultimately show ?thesis using ne by simp
	next
		case None
		obtain as where Some: "ifex_sat t = Some as" using None IF.prems(2) by fastforce
		with IF.prems(2) None have au: "a = as(v1 := True)" by(simp)
		moreover from IF.IH(1)[OF ni(1)] have "as v = False" using Some .
		ultimately show ?thesis using ne by simp
	qed (* feels like this should be easier *)
qed(simp_all add: const_def fun_eq_iff)

lemma ifex_upd_other: "v \<notin> ifex_var_set i \<Longrightarrow> val_ifex i (a(v:=any)) = val_ifex i a" 
proof(induction i)
	case (IF v1 t e)
	have prems: "v \<notin> ifex_var_set t " "v \<notin> ifex_var_set e" using IF.prems by simp_all
	from IF.prems have ne: "v1 \<noteq> v" by clarsimp
	show ?case by(simp only: val_ifex.simps fun_upd_other[OF ne] ifex_vars.simps IF.IH(1)[OF prems(1)] IF.IH(2)[OF prems(2)] split: if_splits)
qed simp_all

(* just thinking\<dots> this basically implies that there can be an order, but doesn't require it *)
fun ifex_no_twice where
"ifex_no_twice (IF v t e) = (
	v \<notin> (ifex_var_set t \<union> ifex_var_set e) \<and>
	ifex_no_twice t \<and> ifex_no_twice e)" |
"ifex_no_twice _ = True"
lemma ordered_ifex_no_twiceI: "ifex_ordered i \<Longrightarrow> ifex_no_twice i"
	by(induction i) (simp_all,blast)

lemma ifex_sat_NoneD: "ifex_sat i = None \<Longrightarrow> val_ifex i ass = False"
	by(induction i) (simp_all split: option.splits)
lemma ifex_sat_SomeD: "ifex_no_twice i \<Longrightarrow> ifex_sat i = Some ass \<Longrightarrow> val_ifex i ass = True"
proof(induction i arbitrary: ass)
	case (IF v t e) 
	have ni: "v \<notin> ifex_var_set t" "v \<notin> ifex_var_set e" using IF.prems(1) by simp_all
	note IF.prems[unfolded ifex_sat.simps]
	thus ?case proof(cases "ifex_sat e")
		case (Some a) thus ?thesis using IF.prems 
			by(clarsimp simp only: val_ifex.simps ifex_sat.simps option.simps fun_upd_same if_False ifex_upd_other[OF ni(2)]) (rule IF.IH(2), simp_all)
	next
		case None
		obtain a where Some: "ifex_sat t = Some a" using None IF.prems(2) by fastforce
		thus ?thesis using IF.prems
			by(clarsimp simp only: val_ifex.simps ifex_sat.simps option.simps fun_upd_same if_True None ifex_upd_other[OF ni(1)])
			(rule IF.IH(1), simp_all)
	qed
qed simp_all
lemma ifex_sat_NoneI: "ifex_no_twice i \<Longrightarrow> (\<And>ass. val_ifex i ass = False) \<Longrightarrow> ifex_sat i = None" 
(* using ifex_sat_SomeD by fastforce *)
proof(rule ccontr)
	case goal1
	from goal1(3) obtain as where "ifex_sat i = Some as" by blast
	from ifex_sat_SomeD[OF goal1(1) this] show False using goal1(2) by simp
qed

end

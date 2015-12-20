theory BDT
imports Boolean_Expression_Checkers BoolFunc
begin

(* datatype 'a ifex = Trueif | Falseif | IF 'a "'a ifex" "'a ifex" *)
(* type_synonym boolfunc2 = "(nat \<Rightarrow> bool) \<Rightarrow> bool" *)


fun ifex_var_set :: "'a ifex \<Rightarrow> 'a set" where
  "ifex_var_set (IF v t e) = {v} \<union> ifex_var_set t \<union> ifex_var_set e" |
  "ifex_var_set Trueif = {}" |
  "ifex_var_set Falseif = {}"

fun ifex_top_var :: "'a ifex \<Rightarrow> 'a option" where
  "ifex_top_var (IF v t e) = Some v" |
  "ifex_top_var Trueif = None" |
  "ifex_top_var Falseif = None"

fun ifex_ordered :: "('a::linorder) ifex \<Rightarrow> bool" where
  "ifex_ordered (IF v t e) = ((\<forall>tv \<in> (ifex_var_set t \<union> ifex_var_set e). v < tv)
                       \<and> ifex_ordered t \<and> ifex_ordered e)" |
  "ifex_ordered Trueif = True" |
  "ifex_ordered Falseif = True"

fun ifex_minimal :: "('a::linorder) ifex \<Rightarrow> bool" where
  "ifex_minimal (IF v t e) = (t \<noteq> e \<and> ifex_minimal t \<and> ifex_minimal e)" |
  "ifex_minimal Trueif = True" |
  "ifex_minimal Falseif = True"

definition bf_ifex_rel where
  "bf_ifex_rel = {(a,b). (\<forall>ass. a ass \<longleftrightarrow> val_ifex b ass) \<and> ifex_ordered b \<and> ifex_minimal b}"

abbreviation ro_ifex where "ro_ifex t \<equiv> ifex_ordered t \<and> ifex_minimal t"

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
  proof(induction arbitrary: v b1 b2)
    case(IF v' b1' b2') thus ?case 
      proof(cases b1', case_tac[!] b2')
        case (goal3 v2 b21 b22) from goal3(4,5) have 0: "w < v'" by simp
        from goal3(2)[OF _ goal3(12)] goal3(3,4,5,12) have "w \<notin> ifex_var_set b2'"
          by force
        from this 0 goal3(6) show ?thesis by simp
      next
        case (goal6 v2 b21 b22) from goal6(4,5) have 0: "w < v'" by simp
        from goal6(2)[OF _ goal6(12)] goal6(3,4,5,12) have "w \<notin> ifex_var_set b2'"
          by force
        from this 0 goal6(6) show ?thesis by simp
      next
        case (goal7 v1 b11 b12) from goal7(4,5) have 0: "w < v'" by simp
        from goal7(1)[OF _ goal7(6)] goal7(3,4,5,6) have "w \<notin> ifex_var_set b1'"
          by force
        from this 0 goal7(12) show ?thesis by simp
      next
        case (goal8 v1 b11 b12) from goal8(4,5) have 0: "w < v'" by simp
        from goal8(1)[OF _ goal8(6)] goal8(3,4,5,6) have "w \<notin> ifex_var_set b1'"
          by force
        from this 0 goal8(12) show ?thesis by simp
      next 
        case (goal9 v1 b11 b12) from goal9(4,5) have 0: "w < v'" by simp
        from goal9(1)[OF _ goal9(6)] goal9(3,4,5,6) have 1: "w \<notin> ifex_var_set b1'"
          by force
        from goal9(2)[OF _ goal9(12)] goal9(3,4,5,12) have "w \<notin> ifex_var_set b2'"
          by force
        from this 0 1 show ?thesis by simp
  qed (auto)
qed(auto)

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
next
case Trueif from this roifex_Trueif_unique show ?case by fastforce
next
case Falseif from this roifex_Falseif_unique show ?case by fastforce
qed
next
case Trueif from this roifex_Trueif_unique show ?case by fastforce
next
case Falseif from this roifex_Falseif_unique show ?case by fastforce
qed

lemma "single_valued bf_ifex_rel" "single_valued (bf_ifex_rel\<inverse>)"
  unfolding single_valued_def bf_ifex_rel_def using ro_ifex_unique by auto

end

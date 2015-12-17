theory BDT
imports Boolean_Expression_Checkers BoolFunc Min2
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

definition ifex_bf2_rel where
  "ifex_bf2_rel = {(a,b). (\<forall>ass. a ass \<longleftrightarrow> val_ifex b ass) \<and> ifex_ordered b \<and> ifex_minimal b}"

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

lemma "(f, b) \<in> ifex_bf2_rel \<Longrightarrow>  b = Trueif \<longleftrightarrow> f = (\<lambda>_. True)"
  unfolding ifex_bf2_rel_def using roifex_Trueif_unique by auto

lemma "(f, b) \<in> ifex_bf2_rel \<Longrightarrow>  b = Falseif \<longleftrightarrow> f = (\<lambda>_. False)"
  unfolding ifex_bf2_rel_def using roifex_Falseif_unique by auto



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

lemma ifex_in_var_set_assign: 
  "ro_ifex b \<Longrightarrow> x \<in> ifex_var_set b \<Longrightarrow> \<exists>ass. val_ifex b ass"
sorry

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

lemma dong: "ro_ifex x \<Longrightarrow> ro_ifex y \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<exists>ass1 ass2. val_ifex x ass1 \<noteq> val_ifex y ass2"
  proof(induction x arbitrary: y)
    case(Trueif) thus ?case 
      proof(cases y)
        case Falseif thus ?thesis by simp
      next
        case (IF) from ro_ifex_false_assign[OF Trueif(2) this] show ?thesis by simp
      qed (auto)
  next
    case(Falseif) thus ?case 
      proof(cases y)
        case Trueif thus ?thesis by simp
      next
        case (IF) from ro_ifex_true_assign[OF Falseif(2) this] show ?thesis by simp
      qed (auto)
  next
    case(IF v b1 b2) note IFind = IF thus ?case
    proof(cases "y")
      case Trueif from ro_ifex_false_assign[OF IFind(3), of v b1 b2] this show ?thesis by simp
    next
      case Falseif from ro_ifex_true_assign[OF IFind(3), of v b1 b2] this show ?thesis by simp
    next
      case (IF yv yb1 yb2) show ?thesis
        proof(cases "yb1 = b1", cases "yb2 = b2")
          case goal1 from this IF IFind(5) have 0: "v \<noteq> yv" by blast
            from goal1 IFind(3) have "v \<notin> ifex_var_set yb1 \<and> v \<notin> ifex_var_set yb2" by auto
            with 0 IF have 2: "v \<notin> ifex_var_set y" by simp
            obtain x where x_def: "x = (IF v b1 b2)" by simp
            from goal1 IF IFind(4) have "yv \<notin> ifex_var_set b1 \<and> yv \<notin> ifex_var_set b2" by auto
            with 0 x_def have 1: "yv \<notin> ifex_var_set x" by simp
            from goal1 IFind(1)[of yb2] IFind(3) 
              obtain a where a_def: "val_ifex b1 a \<noteq> val_ifex yb2 a" by auto
            from roifex_set_var_subtree(1)[OF IFind(3), of v b1 b2] x_def
              have "val_ifex x (a(v := True)) = val_ifex b1 a" by blast
            from this ifex_var_noinfluence[OF 1, of "a(v := True)" "False"]
              have 3: "val_ifex x (a(v := True, yv := False)) = val_ifex b1 a" by fast
            from roifex_set_var_subtree(2)[OF IFind(4) IF, of a] 
                 ifex_var_noinfluence[OF 2, of "a(yv := False)" "True"] 
                 fun_upd_twist[OF 0, of a "True" "False"]
              have 4: "val_ifex y (a(v := True, yv := False)) = val_ifex yb2 a" by presburger
            from 3 4 a_def x_def show ?thesis by blast
        next
          case goal2
            from IFind(3,4) IF IFind(2)[OF _ _ this(2)[symmetric]]  
              obtain a where a_def: "val_ifex b2 a \<noteq> val_ifex yb2 a" by auto
            from IFind(3,4) goal2(1) IF IFind(1)[of yb2] 
              obtain b where b_def: "val_ifex b1 b \<noteq> val_ifex yb2 b" by auto
            from roifex_set_var_subtree(2)[OF IFind(3), of v b1 b2 a]
                  roifex_set_var_subtree(2)[OF IFind(4) IF, of a] a_def
              have 0: "val_ifex (IF v b1 b2) (a(v := False)) \<noteq> val_ifex y (a(yv := False))" by simp
            show ?thesis
              proof(cases "v < yv")
                case True with IFind(4) IF have "v \<notin> ifex_var_set y" 
              next
                case False with goal2
oops

lemma bla: "ro_ifex x \<Longrightarrow> ro_ifex y \<Longrightarrow> \<forall>ass. val_ifex x ass = val_ifex y ass \<Longrightarrow> x = y"
 proof(induction x arbitrary: y)
  case (IF xv xb1 xb2) note IFind = IF thus ?case
    proof(cases y)
      case (IF yv yb1 yb2)
  thm IF IFind(3,4,5) IFind(1)[of yb1] IFind(2)[of yb2]
  obtain x where x_def: "x = IF xv xb1 xb2" by simp
  from this IFind(3,4) IF have 0: "ro_ifex xb1" "ro_ifex xb2" "ro_ifex yb1" "ro_ifex yb2" 
                                  "ro_ifex x" by auto
  from IF IFind(5) x_def have 1: "\<forall>ass. val_ifex x ass = val_ifex y ass" by simp
  show ?thesis proof(cases "xv = yv")
    note roifex_set_var_subtree(1)[OF 0(5) x_def, symmetric]
    case True 
      from roifex_set_var_subtree(1)[OF 0(5) x_def]
           roifex_set_var_subtree(1)[OF IFind(4) IF] 1 True IFind(1)[OF 0(1) 0(3)]
           have 3: "xb1 = yb1" by blast
      from roifex_set_var_subtree(2)[OF 0(5) x_def]
           roifex_set_var_subtree(2)[OF IFind(4) IF] 1 True IFind(2)[OF 0(2) 0(4)]
           have 4: "xb2 = yb2" by blast
      from True 3 4 IF show ?thesis by simp
    next
    case False note uneq = False show ?thesis
      proof(cases "xv < yv")
        case True
          from ifex_ordered_not_part[OF _ IF True] ifex_var_noinfluence[of xv y _ "True"]
               IFind(4) roifex_set_var_subtree(1)[OF 0(5) x_def] 1
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
          from this uneq have "yv < xv" by auto
          from ifex_ordered_not_part[OF _ x_def this] ifex_var_noinfluence[of yv x _ "True"]
               0(5) roifex_set_var_subtree(1)[OF IFind(4) IF] 1
             have 5: "\<And>ass. val_ifex yb1 ass = val_ifex y ass" by blast
          from IF IFind(4) ifex_var_noinfluence[of yv yb1 _ "False"] 
               ifex_var_noinfluence[of yv yb2 _ "False"]
            have "\<And>ass. val_ifex yb1 (ass(yv := False)) = val_ifex yb1 ass"
                 "\<And>ass. val_ifex yb2 (ass(yv := False)) = val_ifex yb2 ass" by auto
          from 5 this roifex_set_var_subtree(2)[OF IFind(4) IF]
            have "\<And>ass. val_ifex yb1 ass = val_ifex yb2 ass" by presburger
          from IFind(1)[OF 0(1) 0(2)] this IFind(3) have "False" by auto
          from this show ?thesis ..
oops

end

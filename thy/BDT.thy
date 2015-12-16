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

lemma "ro_ifex b \<Longrightarrow> x \<in> ifex_var_set b \<Longrightarrow>
       \<exists>ass. val_ifex b (ass(x:=True)) \<noteq> val_ifex b (ass(x:=False))"
oops

lemma "ro_ifex x \<Longrightarrow> ro_ifex y \<Longrightarrow> \<forall>ass. val_ifex x ass = val_ifex y ass \<Longrightarrow> x = y"
  proof(induction x arbitrary: y)
  case (IF xv xb1 xb2) note IFinduction = IF thus ?case
    proof(cases y)
      case (IF yv yb1 yb2) 
  thm IF IFinduction(3,4,5) IFinduction(1)[of yb1] IFinduction(2)[of yb2]
  from IF IFinduction(5) have 0: "\<forall>ass. val_ifex (IF xv xb1 xb2) ass = val_ifex (IF yv yb1 yb2) ass"
   by simp
oops

end

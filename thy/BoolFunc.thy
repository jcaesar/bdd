theory BoolFunc
imports Main
begin

type_synonym 'a boolfunc = "('a \<Rightarrow> bool) \<Rightarrow> bool"

definition "bf_ite i t e \<equiv> (\<lambda>l. if i l then t l else e l)"

definition "bf_restrict (i::'a) (val::bool) (f::'a boolfunc) \<equiv> (\<lambda>v. f (v(i:=val)))"

lemma brace90shannon: "bf_ite F G H ass =
  bf_ite (\<lambda>l. l i) 
	       (bf_ite (bf_restrict i True F) (bf_restrict i True G) (bf_restrict i True H))
	       (bf_ite (bf_restrict i False F) (bf_restrict i False G) (bf_restrict i False H)) ass"
unfolding bf_ite_def bf_restrict_def by (auto simp add: fun_upd_idem)

end
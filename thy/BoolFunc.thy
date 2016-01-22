section{* Boolean functions *}
theory BoolFunc
imports Main
begin
text{*
	General thoughts on infinite arity boolean functions
*}
type_synonym 'a boolfunc = "('a \<Rightarrow> bool) \<Rightarrow> bool"

text{* if-then-else on boolean functions. *}
definition "bf_ite i t e \<equiv> (\<lambda>l. if i l then t l else e l)"
text{* if-then-else is interesting because we can, together with constant true and false, represent all binary boolean functions using maximally two applications of it. *}
definition "bf_True \<equiv> (\<lambda>l. True)"
definition "bf_False \<equiv> (\<lambda>l. False)"
text{* A quick demonstration *}
definition "bf_and a b \<equiv> bf_ite a b bf_False"
lemma "(bf_and a b) as \<longleftrightarrow> a as \<and> b as" unfolding bf_and_def  bf_ite_def bf_False_def bf_True_def by meson 
definition "bf_not b \<equiv> bf_ite b bf_False bf_True"
lemma "bf_not a as \<longleftrightarrow> \<not>a as" unfolding bf_not_def bf_ite_def bf_False_def bf_True_def by meson


subsection{* Shannon decomposition *}
text{*
	A restriction of a boolean function on a variable is creating the boolean function that evaluates as if that variable was set to a fixed value
*}
definition "bf_restrict (i::'a) (val::bool) (f::'a boolfunc) \<equiv> (\<lambda>v. f (v(i:=val)))"

text {*
	Restrictions are useful, because they remove variables from the set of significant variables
*}
definition "bf_vars bf = {v. \<exists>as. bf_restrict v True bf as \<noteq> bf_restrict v False bf as}"
lemma "var \<notin> bf_vars (bf_restrict var val ex)"
unfolding bf_vars_def bf_restrict_def by(simp)

text{*
	We can decompose calculating if-then-else into computing if-then-else of two triples functions with one variable restricted to true / false.
	Given that the functions have finite arity, we can use this to construct a recursive definition.
*}
lemma brace90shannon: "bf_ite F G H ass =
  bf_ite (\<lambda>l. l i) 
	       (bf_ite (bf_restrict i True F) (bf_restrict i True G) (bf_restrict i True H))
	       (bf_ite (bf_restrict i False F) (bf_restrict i False G) (bf_restrict i False H)) ass"
unfolding bf_ite_def bf_restrict_def by (auto simp add: fun_upd_idem)


end

theory FormulaIfex
  imports BDT
begin

datatype (atoms: 'a) formula =
    Atom 'a
  | Bot                              ("\<bottom>")  
  | Not "'a formula"                 ("\<^bold>\<not>")
  | And "'a formula" "'a formula"    (infix "\<^bold>\<and>" 68)
  | Or "'a formula" "'a formula"     (infix "\<^bold>\<or>" 68)
  | Imp "'a formula" "'a formula"    (infixr "\<^bold>\<rightarrow>" 68)

type_synonym 'a valuation = "'a \<Rightarrow> bool"
primrec formula_semantics :: "'a valuation \<Rightarrow> 'a formula \<Rightarrow> bool" (infix "\<Turnstile>" 51) where
"\<A> \<Turnstile> Atom k = \<A> k" |
"_ \<Turnstile> \<bottom> = False" |
"\<A> \<Turnstile> Not F = (\<not> \<A> \<Turnstile> F)" |
"\<A> \<Turnstile> And F G = (\<A> \<Turnstile> F \<and> \<A> \<Turnstile> G)" |
"\<A> \<Turnstile> Or F G = (\<A> \<Turnstile> F \<or> \<A> \<Turnstile> G)" |
"\<A> \<Turnstile> Imp F G = (\<A> \<Turnstile> F \<longrightarrow> \<A> \<Turnstile> G)"

fun mk_ifex :: "('a :: linorder) formula \<Rightarrow> 'a ifex" where
"mk_ifex (Atom a) = IF a Trueif Falseif" |
"mk_ifex Bot = Falseif" |
"mk_ifex (Not f) = ifex_ite (mk_ifex f) Falseif Trueif" |
"mk_ifex (And f g) = ifex_ite (mk_ifex f) (mk_ifex g) Falseif" |
"mk_ifex (Or f g) = ifex_ite (mk_ifex f) Trueif (mk_ifex g)" |
"mk_ifex (Imp f g) = ifex_ite (mk_ifex f) (mk_ifex g) Trueif"

lemma ord: "ifex_ordered (mk_ifex f)"
  by(induction rule: mk_ifex.induct) (insert order_ifex_ite_invar; fastforce)+

lemma min: "ifex_minimal (mk_ifex f)"
  by(induction rule: mk_ifex.induct) (insert minimal_ifex_ite_invar; fastforce)+

theorem "assmt \<Turnstile> f \<longleftrightarrow> val_ifex (mk_ifex f) assmt"
  apply(induction f)
  apply(simp_all)[2]
     apply(subst mk_ifex.simps; subst val_ifex_ite_subst; simp_all add: min ord bf_ite_def val_ifex_ite_subst)+
  done
  
end
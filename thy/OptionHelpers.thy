theory OptionHelpers
imports Main "~~/src/HOL/Library/Monad_Syntax"
begin


primrec oassert :: "bool \<Rightarrow> unit option" where
  "oassert True = Some ()" | "oassert False = None"

lemma oassert_iff[simp]: 
  "oassert \<Phi> = Some x \<longleftrightarrow> \<Phi>" 
  "oassert \<Phi> = None \<longleftrightarrow> \<not>\<Phi>"  
  by (cases \<Phi>) auto

primrec ospec :: "('a option) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "ospec None _ = False"
| "ospec (Some v) Q = Q v"

named_theorems ospec_rules

lemma oreturn_rule[ospec_rules]: "\<lbrakk> P r \<rbrakk> \<Longrightarrow> ospec (Some r) P" by simp

lemma obind_rule[ospec_rules]: "\<lbrakk> ospec m Q; \<And>r. Q r \<Longrightarrow> ospec (f r) P \<rbrakk> \<Longrightarrow> ospec (m\<guillemotright>=f) P"
  apply (cases m)
  apply (auto split: Option.bind_splits)
  done

lemma ospec_alt: "ospec m P = (case m of None \<Rightarrow> False | Some x \<Rightarrow> P x)"
  by (auto split: option.splits)

lemma ospec_bind_simp: "ospec (m\<guillemotright>=f) P \<longleftrightarrow> (ospec m (\<lambda>r. ospec (f r) P))"
  apply (cases m)
  apply (auto split: Option.bind_splits)
  done

lemma ospec_cons: 
  assumes "ospec m Q"
  assumes "\<And>r. Q r \<Longrightarrow> P r"
  shows "ospec m P"
  using assms by (cases m) auto

lemma oreturn_synth: "ospec (Some x) (\<lambda>r. r=x)" by simp

lemma ospecI: "ospec x P \<Longrightarrow> x = Some y \<Longrightarrow> P y" by simp

end
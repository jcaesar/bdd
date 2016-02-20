section{* Collapsing the levels *}
theory LevelCollapse
imports Conc_Impl
begin
text{* 
The theory up to this point is implemented in a way that separated the different aspects into different levels.
This is highly beneficial for us, since it allows us to tackle the difficulties arising in small chunks.
However, exporting this to the user would be highly impractical.
Thus, this theory collapses all the different levels (i.e. refinement steps) and relates the computations in the heap monad to 
@{type boolfunc}.
*}

definition "bddmi_rel cs \<equiv> {(a,c)|a b c. (a,b) \<in> bf_ifex_rel \<and> (c,b) \<in> Rmi cs}"
definition "bdd_relator p s \<equiv> \<exists>\<^sub>Acs. is_bdd_impl cs s * \<up>(p \<subseteq> (bddmi_rel cs) \<and> bdd_sane cs)"

text{*
The @{type assn} predicate @{term bdd_relator} is the interface that is exposed to the user.
(The contents of the definition are not exposed.)
*}

lemma bdd_relator_mono: "q \<subseteq> p \<Longrightarrow> bdd_relator p s \<Longrightarrow>\<^sub>A bdd_relator q s" unfolding bdd_relator_def by sep_auto

thm bdd_relator_def[unfolded bddmi_rel_def, simplified]
lemma join_hlp1: "is_bdd_impl a s * is_bdd_impl b s \<Longrightarrow>\<^sub>A is_bdd_impl a s * is_bdd_impl b s * \<up>(a = b)"
	apply clarsimp
	apply(rule preciseD[where p=s and R="is_bdd_impl" and F="is_bdd_impl b s" and F'="is_bdd_impl a s"])
	 apply(rule is_bdd_impl_prec)
	apply(unfold mod_and_dist)
	apply(rule conjI)
	apply assumption
	apply(simp add: star_aci(2))
done

lemma join_hlp: "is_bdd_impl a s * is_bdd_impl b s = is_bdd_impl b s * is_bdd_impl a s * \<up>(a = b)"
	apply(rule ent_iffI[rotated])
	apply simp
	apply(rule ent_trans)
	 apply(rule join_hlp1)
	apply(simp)
done

lemma add_true_asm:
	assumes "<b * true> p <a>\<^sub>t"
	shows "<b> p <a>\<^sub>t"
	apply(rule cons_pre_rule)
	prefer 2
	apply(rule assms)
	apply(simp add: ent_true_drop)
done

lemma add_anything:
	assumes "<b> p <a>"
	shows "<b * x> p <\<lambda>r. a r * x>\<^sub>t"
proof -
	note [sep_heap_rules] = assms
	show ?thesis by sep_auto
qed

lemma add_true:
	assumes "<b> p <a>\<^sub>t"
	shows "<b * true> p <a>\<^sub>t"
	using assms add_anything[where x=true] by force

thm iteci_rule[THEN mp] brofix.ite_impl_R ifex_ite_rel_bf
lemma iteci_rule[sep_heap_rules]: "
\<lbrakk>(ib, ic) \<in> rp; (tb, tc) \<in> rp; (eb, ec) \<in> rp\<rbrakk> \<Longrightarrow>
<bdd_relator rp s> 
	iteci ic tc ec s
<\<lambda>(r,s'). bdd_relator (insert (bf_ite ib tb eb,r) rp) s'>\<^sub>t"
	apply(unfold bdd_relator_def)
	apply(intro norm_pre_ex_rule)
	apply(clarsimp)
	apply(unfold bddmi_rel_def)
	apply(drule (1) rev_subsetD)+
	apply(clarsimp)
	apply(drule (3) brofix.ite_impl_R[where ii=ic and ti=tc and ei=ec, unfolded in_rel_def])
	apply(drule ospecD2)
	apply(clarsimp simp del: ifex_ite.simps)
	apply(rule cons_post_rule)
	 apply(rule cons_pre_rule)
	  prefer 2
	  apply(rule iteci_rule[THEN mp, THEN add_true])
	  apply(assumption)
	 apply(sep_auto; fail)
	apply(clarsimp simp del: ifex_ite.simps)
	apply(rule ent_ex_postI)
	apply(subst ent_pure_post_iff)
	apply(rule conjI[rotated])
	 apply(sep_auto; fail)
	apply(clarsimp simp del: ifex_ite.simps)
	apply(rule conjI[rotated])
	 apply(force simp add: brofix.les_def)
	apply(rule exI)
	apply(rule conjI)
	 apply(erule (2) ifex_ite_rel_bf[unfolded in_rel_def])
	apply assumption
done

lemma tci_rule[sep_heap_rules]:
"<bdd_relator rp s> 
	tci s
<\<lambda>(r,s'). bdd_relator (insert (bf_True,r) rp) s'>\<^sub>t"
	apply(unfold bdd_relator_def)
	apply(intro norm_pre_ex_rule)
	apply(clarsimp)
	apply(frule brofix.Timpl_rule)
	apply(drule ospecD2)
	apply(clarify)
	apply(sep_auto)
	 apply(unfold bddmi_rel_def)
	 apply(clarsimp)
	apply(force simp add: brofix.les_def)
done

lemma fci_rule[sep_heap_rules]:
"<bdd_relator rp s> 
	fci s
<\<lambda>(r,s'). bdd_relator (insert (bf_False,r) rp) s'>\<^sub>t"
	apply(unfold bdd_relator_def)
	apply(intro norm_pre_ex_rule)
	apply(clarsimp)
	apply(frule brofix.Fimpl_rule)
	apply(drule ospecD2)
	apply(clarify)
	apply(sep_auto)
	 apply(unfold bddmi_rel_def)
	 apply(clarsimp)
	apply(force simp add: brofix.les_def)
done

text{* IFC/ifmi/ifci require that the variable order is ensured by the user. 
Instead of using ifci, a combination of litci and iteci have to be used. *}
lemma [sep_heap_rules]:
"\<lbrakk>(tb, tc) \<in> rp; (eb, ec) \<in> rp\<rbrakk> \<Longrightarrow>
<bdd_relator rp s> 
	ifci v tc ec s
<\<lambda>(r,s'). bdd_relator (insert (bf_if v tb eb,r) rp) s'>\<^sub>t"
(*
	apply(unfold bdd_relator_def)
	apply(intro norm_pre_ex_rule)
	apply(unfold bddmi_rel_def)
	apply(clarsimp)
	apply(drule (1) rev_subsetD)+
	apply(clarsimp)
	apply(frule (2) brofix.IFimpl_rule[of _ tc _ ec])
	apply(drule ospecD2)
	apply(clarify)
	apply(sep_auto)
	
	 apply(unfold bddmi_rel_def)
	 apply(clarsimp)
	 apply(rule_tac x = Falseif in exI) (* okay, now I'm starting to prove something new, which I shouldn't *)
	 apply(auto simp add: bf_False_def bf_ifex_rel_def)[1]
	apply(force sim p add: brofix.les_def)*)
oops
lemma notci_rule[sep_heap_rules]:
	assumes "(tb, tc) \<in> rp"
	shows "<bdd_relator rp s> notci tc s <\<lambda>(r,s'). bdd_relator (insert (bf_not tb,r) rp) s'>\<^sub>t"
using assms
	apply(unfold bf_not_def notci_def)
	apply(rule bind_rule, rule fci_rule, clarify)
	apply(rule bind_rule, rule tci_rule[THEN add_true], clarify)
	apply(rule cons_post_rule)
	apply(rule iteci_rule[THEN add_true]; blast)
	apply(rule fr_refl)
	apply(clarify)
	apply(rule bdd_relator_mono; fast)
done

lemma cirules1[sep_heap_rules]:
	assumes "(tb, tc) \<in> rp" "(eb, ec) \<in> rp"
	shows
		"<bdd_relator rp s> andci tc ec s <\<lambda>(r,s'). bdd_relator (insert (bf_and tb eb,r) rp) s'>\<^sub>t"
		"<bdd_relator rp s> orci tc ec s <\<lambda>(r,s'). bdd_relator (insert (bf_or tb eb,r) rp) s'>\<^sub>t"
		"<bdd_relator rp s> biimpci tc ec s <\<lambda>(r,s'). bdd_relator (insert (bf_biimp tb eb,r) rp) s'>\<^sub>t"
		"<bdd_relator rp s> xorci tc ec s <\<lambda>(r,s'). bdd_relator (insert (bf_xor tb eb,r) rp) s'>\<^sub>t"
(* actually, these functions would allow for more insert. I think that would be inconvenient though. *)
using assms
by(unfold bf_and_def andci_def bf_or_def orci_def bf_nand_def biimpci_def bf_biimp_def xorci_def bf_xor_alt)
  (rule bind_rule, (rule fci_rule | rule tci_rule | (rule notci_rule; assumption)); clarify, rule cons_post_rule, (rule iteci_rule[THEN add_true]; blast), 
	rule fr_refl; clarify, (rule bdd_relator_mono; fast))+
(* Because I can, that's why. (see below for the unfolded version) *)

lemma cirules2[sep_heap_rules]:
	assumes "(tb, tc) \<in> rp" "(eb, ec) \<in> rp"
	shows
		"<bdd_relator rp s> nandci tc ec s <\<lambda>(r,s'). bdd_relator (insert (bf_nand tb eb,r) rp) s'>\<^sub>t"
		"<bdd_relator rp s> norci tc ec s <\<lambda>(r,s'). bdd_relator (insert (bf_nor tb eb,r) rp) s'>\<^sub>t"
	using assms
	by(sep_auto intro!: fr_refl bdd_relator_mono simp: nandci_def bf_nand_def norci_def bf_nor_def)+
(* in case sep_auto starts acting up here like it does in the proof above:
apply(rule bind_rule)
apply(rule cirules1(2,1); assumption)
apply(clarify)
apply(rule cons_post_rule)
apply(rule notci_rule[THEN add_true]; blast)
apply(rule fr_refl)
apply(clarify)
apply(rule bdd_relator_mono)
apply(fast)
*)

lemma litci_rule[sep_heap_rules]:
	"<bdd_relator rp s> litci v s <\<lambda>(r,s'). bdd_relator (insert (bf_lit v,r) rp) s'>\<^sub>t"
using assms
	apply(unfold litci_def)
	apply(subgoal_tac "\<And>t ab bb.
		   <bdd_relator (insert (bf_False, ab) (insert (bf_True, t) rp)) bb *
			true> ifci v t ab bb <\<lambda>r. case r of (r, x) \<Rightarrow> bdd_relator (insert (bf_lit v, r) rp) x>\<^sub>t")
	 apply(sep_auto; fail)
	apply(rename_tac tc fc sc)
	apply(unfold bdd_relator_def[abs_def])
	apply(clarsimp)
	apply(intro norm_pre_ex_rule)
	apply(clarsimp)
	apply(unfold bddmi_rel_def)
	apply(clarsimp simp only: bf_ifex_rel_consts_ensured)
	apply(rename_tac tc fc sc sm a aa b ba fm tm)
	apply(frule_tac brofix.IFimpl_rule)
	  apply(thin_tac "(fm, Falseif) \<in> Rmi sm") apply(assumption) apply(assumption) (* sorry for the hacky hack, I don't know how to instantiate IFimpl_rule *)
	apply(clarsimp)
	apply(drule ospecD2)
	apply(clarify)
	apply(sep_auto)
	apply(force simp add: brofix.les_def)
done

lemma tautci_rule[sep_heap_rules]:
	shows "(tb, tc) \<in> rp \<Longrightarrow> <bdd_relator rp s> tautci tc s <\<lambda>r. bdd_relator rp s * \<up>(r \<longleftrightarrow> tb = bf_True)>\<^sub>t"
	apply(unfold tautci_def)
	apply(unfold bdd_relator_def)
	apply(intro norm_pre_ex_rule; clarsimp)
	apply(unfold bddmi_rel_def)
	apply(drule (1) rev_subsetD)
	apply(clarsimp)
	apply(rename_tac sm ti)
	apply(case_tac ti; clarify; frule (1) brofix.DESTRimpl_rules; drule ospecD2; clarify)
	  apply(sep_auto; fail)
	 apply(sep_auto; simp add: bf_False_def bf_True_def fun_eq_iff; fail)
	apply(sep_auto)
done

lemma emptyci_rule[sep_heap_rules]:
	shows "<emp> emptyci <\<lambda>r. bdd_relator {} r>\<^sub>t"
by(sep_auto simp: bdd_relator_def)

(* At some point in history, I've got to make sure that all those emptyci_rule and firends don't appear duplicate.
   Today is not this day. *)

(* I had some nice code_printing setup here, to implement blita/blit'. But that only did what would have been generated anyway *)
lemma [code del]:
    "blit src si dst di len
      = blit' src (integer_of_nat si) dst (integer_of_nat di)
          (integer_of_nat len)" by (simp add: blit'_def)
declare blit_def[code]

(* Todo: verify iteci_opt *)
export_code open iteci_opt iteci notci andci orci nandci norci biimpci xorci ifci tci fci tautci emptyci graphifyci litci in Haskell module_name IBDD file "../hs/gen"
  
(* value "do { e \<leftarrow> emptyci; (graphifyci ''asdf'' 1 e) }" hm. *)

end

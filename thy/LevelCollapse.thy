theory LevelCollapse
imports Conc_Impl
begin

definition "bddmi_rel cs \<equiv> {(a,c)|a b c. (a,b) \<in> bf_ifex_rel \<and> (c,b) \<in> Rmi cs}"
definition "bdd_relator p s \<equiv> \<exists>\<^sub>Acs. is_bdd_impl cs s * \<up>(p \<subseteq> (bddmi_rel cs) \<and> bdd_sane cs)"

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
(* Yeah, this is rubbish. *)
lemma "
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

(* I had some nice code_printing setup here, to implement blita/blit'. But that only did what would have been generated anyway *)
lemma [code del]:
    "blit src si dst di len
      = blit' src (integer_of_nat si) dst (integer_of_nat di)
          (integer_of_nat len)" by (simp add: blit'_def)
declare blit_def[code]

(* Todo: Verify all of these\<dots>, except graphifyci *)
export_code open iteci_opt iteci notci andci orci nandci norci biimpci xorci ifci tci fci tautci emptyci graphifyci litci in Haskell module_name IBDD file "../hs/gen"
  
(* value "do { e \<leftarrow> emptyci; (graphifyci ''asdf'' 1 e) }" hm. *)

end

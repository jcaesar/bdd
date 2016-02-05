theory LevelCollapse
imports Conc_Impl
begin

definition "bddmi_rel cs \<equiv> {(a,c)|a b c. (a,b) \<in> bf_ifex_rel \<and> (c,b) \<in> Rmi cs \<and> bdd_sane cs}"
definition "bdd_relator a d s \<equiv> \<exists>\<^sub>Acs. is_bdd_impl cs s * \<up>(in_rel (bddmi_rel cs) a d)"
(* I know, I know\<dots> *)

thm bdd_relator_def[unfolded bddmi_rel_def, simplified]
lemma join_hlp1: "is_bdd_impl a s * is_bdd_impl b s \<Longrightarrow>\<^sub>A is_bdd_impl a s * is_bdd_impl b s * \<up>(a = b)"
unfolding is_bdd_impl_def
	apply clarsimp
	apply(rule preciseD[where p=s and R="is_pointermap_impl" and F="is_pointermap_impl b s" and F'="is_pointermap_impl a s"])
	 apply(rule is_pointermap_impl_prec)
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
<bdd_relator ib ic s * bdd_relator tb tc s * bdd_relator eb ec s> 
	iteci ic tc ec s
<\<lambda>(r,s'). bdd_relator (bf_ite ib tb eb) r s'>\<^sub>t"
	apply(unfold bdd_relator_def)
	apply(simp)
	apply(intro norm_pre_ex_rule)
	apply(clarsimp)
	apply(unfold bddmi_rel_def)
	apply(rename_tac cse cst csi)
	apply(unfold star_assoc)
	apply(subst join_hlp)
	apply(unfold star_assoc[symmetric])
	apply(subst join_hlp)
	apply(clarsimp)
	apply(drule (3) brofix.ite_impl_R[where ii=ic and ti=tc and ei=ec, unfolded in_rel_def])
	apply(drule ospecD2)
	apply(clarsimp simp del: ifex_ite.simps)
	apply(rule cons_post_rule)
	 apply(rule cons_pre_rule)
	  prefer 2
	  apply(rule iteci_rule[THEN mp, THEN add_true])
	  apply(assumption)
	 apply(sep_auto)
	apply(clarsimp simp del: ifex_ite.simps)
	apply(rule ent_ex_postI)
	apply(subst ent_pure_post_iff)
	apply(rule conjI)
	 prefer 2
	 apply(sep_auto)
	apply(clarsimp simp del: ifex_ite.simps)
	apply(rule exI)
	apply(rule conjI)
	 apply(erule (2) ifex_ite_rel_bf[unfolded in_rel_def])
	apply assumption
done

(* Todo: Verify all of these\<dots>, except graphifyci *)
export_code open iteci notci andci orci ifci tci fci emptyci graphifyci in Haskell module_name IBDD file "output"

value "do { e \<leftarrow> emptyci; (graphifyci ''asdf'' 1 e) }" (* hm. *)

end
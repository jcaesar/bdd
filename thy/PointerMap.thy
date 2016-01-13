theory PointerMap
imports Main
begin

record 'a pointermap = 
	entries :: "'a list"
	getentry :: "'a \<Rightarrow> nat option"
	
definition "pointermap_sane m \<equiv> (distinct (entries m) \<and> (\<forall>n \<in> {..<length (entries m)}. getentry m (entries m ! n) = Some n) \<and> (\<forall>p i. getentry m p = Some i \<longrightarrow> entries m ! i = p \<and> i < length (entries m)))"

definition "pointermap_insert a m \<equiv> \<lparr>entries = (entries m)@[a], getentry = (getentry m)(a \<mapsto> length (entries m))\<rparr>"

definition "pm_pth m p \<equiv> entries m ! p"

definition "pointermap_p_valid p m \<equiv> p < length (entries m)"

definition "pointermap_getmk a m \<equiv> (case getentry m a of Some p \<Rightarrow> (p,m) | None \<Rightarrow> let u = pointermap_insert a m in (the (getentry u a), u))"  

lemma conjI2: "P \<Longrightarrow> Q \<Longrightarrow> Q \<and> P" ..
lemma pointermap_sane_appendD: "pointermap_sane s \<Longrightarrow> m \<notin> set (entries s) \<Longrightarrow> pointermap_sane (pointermap_insert m s)"
unfolding pointermap_sane_def pointermap_insert_def
proof(rule conjI2, rule conjI2)
	case goal3 thus ?case by simp
next
	case goal2 thus ?case 
	apply(unfold Ball_def) 
	apply(rule)
	apply(rule)
	apply(rename_tac n)
	apply(case_tac "n < length (entries s)")
	proof -
		case goal1 
		from goal1(4) have sa: "\<And>a. (entries s @ a) ! n = entries s ! n" by (simp add: nth_append)
		from goal1(1,4) have ih: "getentry s (entries s ! n) = Some n" by simp
		from goal1(2,4) have ne: "entries s ! n \<noteq> m" using nth_mem by fastforce
		from sa ih ne show ?case by simp
	next
		case goal2
		from goal2(3,4) have ln: "n = length (entries s)" by simp
		hence sa: "\<And>a. (entries s @ [a]) ! n = a" by simp
		from sa ln show ?case by simp
	qed
next
	case goal1 thus ?case
		apply(auto simp add: nth_append fun_upd_same Ball_def)
		apply(force)
	done
qed

lemma luentries_noneD: "getentry s a = None \<Longrightarrow> pointermap_sane s \<Longrightarrow> a \<notin> set (entries s)"
unfolding pointermap_sane_def
proof
	case goal1
	from goal1(3) obtain n where "n < length (entries s)" "entries s ! n = a" unfolding in_set_conv_nth by blast
	with goal1(2,1) show False by force
qed

lemma pm_pth_append: "pointermap_p_valid p m \<Longrightarrow> pm_pth (pointermap_insert a m) p = pm_pth m p"
	unfolding pointermap_p_valid_def pm_pth_def pointermap_insert_def
	by(simp add: nth_append)

lemma pointermap_insert_in: "u = (pointermap_insert a m) \<Longrightarrow> pm_pth u (the (getentry u a)) = a"
unfolding pointermap_insert_def pm_pth_def
by(simp)

lemma pointermap_insert_p_validI: "pointermap_p_valid p m \<Longrightarrow> pointermap_p_valid p (pointermap_insert a m)"
	unfolding pointermap_insert_def pointermap_p_valid_def
	by simp

thm nth_eq_iff_index_eq
lemma pth_eq_iff_index_eq: "pointermap_sane m \<Longrightarrow> pointermap_p_valid p1 m \<Longrightarrow> pointermap_p_valid p2 m \<Longrightarrow> (pm_pth m p1 = pm_pth m p2) \<longleftrightarrow> (p1 = p2)"
	unfolding pointermap_sane_def pointermap_p_valid_def pm_pth_def
	using nth_eq_iff_index_eq by blast
	
lemma pointermap_p_valid_updateI: "pointermap_sane m \<Longrightarrow> getentry m a = None \<Longrightarrow> u = pointermap_insert a m \<Longrightarrow> p = the (getentry u a) \<Longrightarrow> pointermap_p_valid p u"
by(simp add: pointermap_sane_def pointermap_p_valid_def pointermap_insert_def)

lemma pointermap_get_validI: "pointermap_sane m \<Longrightarrow> getentry m a = Some p \<Longrightarrow> pointermap_p_valid p m"
by(simp add: pointermap_sane_def pointermap_p_valid_def)

lemma pointermap_sane_getmkD: 
	assumes sn: "pointermap_sane m"
	assumes res: "pointermap_getmk a m = (p,u)"
	shows "pointermap_sane u \<and> pointermap_p_valid p u"
using sn res[symmetric]
	apply(cases "getentry m a")
	apply(simp_all add: pointermap_getmk_def Let_def split: option.split)
	 apply(rule)
	  apply(rule pointermap_sane_appendD)
	   apply(clarify;fail)+
	  apply(rule luentries_noneD)
	apply(clarify;fail)+
	 apply(rule pointermap_p_valid_updateI[OF _ _ refl refl])
	  apply(clarify;fail)+
	apply(erule pointermap_get_validI)
	apply(simp)
done

lemma pointermap_update_pthI: 
	assumes sn: "pointermap_sane m"
	assumes res: "pointermap_getmk a m = (p,u)"
	shows "pm_pth u p = a"
using assms
	apply(simp add: pointermap_getmk_def Let_def split: option.splits)
	 apply(meson pointermap_insert_in)
	apply(clarsimp simp: pointermap_sane_def pm_pth_def)
done

lemma pointermap_p_valid_inv:
	assumes "pointermap_p_valid p m"
	assumes "pointermap_getmk a m = (x,u)"
	shows "pointermap_p_valid p u"
using assms
by(simp add: pointermap_getmk_def Let_def split: option.splits) (meson pointermap_insert_p_validI)

lemma pointermap_p_pth_inv:
	assumes pv: "pointermap_p_valid p m"
	assumes u: "pointermap_getmk a m = (x,u)"
	shows "pm_pth u p = pm_pth m p"
using pm_pth_append[OF pv] u
by(clarsimp simp: pointermap_getmk_def Let_def split: option.splits)

end
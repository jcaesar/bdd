theory BDT
imports Boolean_Expression_Checkers
        "../thy/BoolFunc"
begin

(* datatype 'a ifex = Trueif | Falseif | IF 'a "'a ifex" "'a ifex" *)
(* type_synonym boolfunc2 = "(nat \<Rightarrow> bool) \<Rightarrow> bool" *)


fun ifex_variable_set :: "'a ifex \<Rightarrow> 'a set" where
  "ifex_variable_set (IF v t e) = {v} \<union> ifex_variable_set t \<union> ifex_variable_set e" |
  "ifex_variable_set Trueif = {}" |
  "ifex_variable_set Falseif = {}"

fun ordner :: "('a::linorder) ifex \<Rightarrow> bool" where
  "ordner (IF v t e) = ((\<forall>tv \<in> (ifex_variable_set t \<union> ifex_variable_set e). v < tv)
                       \<and> ordner t \<and> ordner e)" |
  "ordner Trueif = True" |
  "ordner Falseif = True"

definition ifex_bf2_rel where
  "ifex_bf2_rel = {(a,b). (\<forall>ass. a ass \<longleftrightarrow> val_ifex b ass) \<and> ordner b}"

(* had we done ifex_variable_list instead of _set, we would have gotten out way easier\<dots> *)
definition "is_lowest_element e S = (e \<in> S \<and> (\<forall>oe \<in> S. e \<le> oe))"
definition select_lowest :: "'a set \<Rightarrow> 'a :: linorder" where "select_lowest a = the_elem {m. m \<in> a \<and> (\<forall>om \<in> a. m \<le> om)}"
lemma select_hlp_ex: "finite (S :: ('a :: linorder) set)  \<Longrightarrow> S \<noteq> {} \<Longrightarrow> \<exists>k. k \<in> {m. m \<in> S \<and> (\<forall>om \<in> S. m \<le> om)}"
using Min.coboundedI Min_in mem_Collect_eq by blast
lemma card2: "2 \<le> card (S :: ('a :: linorder) set) \<Longrightarrow> \<exists>a b. a \<in> S \<and> b \<in> S \<and> a < b"
proof - (* might be more beautifully reprovable under the use of *) thm card_eq_SucD
	assume a: "2 \<le> card S"
	then obtain x where x: "x \<in> S" using card_eq_0_iff by fastforce
	then obtain S' where S': "x \<notin> S'" "S = S' \<union> {x}" using mk_disjoint_insert by force
	with a have "1 \<le> card S'" by (metis One_nat_def Suc_1 Un_insert_right card_infinite card_insert_disjoint finite_Un not_less_eq_eq one_le_numeral sup_bot.right_neutral)
	then obtain y where y: "y \<in> S'" using card_eq_0_iff by fastforce
	then have "x \<noteq> y" "y \<in> S" using S' by blast+
	with x show ?thesis by (meson neq_iff)
qed
lemma select_set_ov: "finite a \<Longrightarrow> (a :: ('a :: linorder) set) \<noteq> {} \<Longrightarrow> card {m. m \<in> a \<and> (\<forall>om \<in> a. m \<le> om)} = 1"
proof(rule ccontr)
	let ?m = "{m \<in> a. \<forall>om\<in>a. m \<le> om}"
	case goal1
	then obtain ae where ae: "ae \<in> a" by blast
	note select_hlp_ex[OF goal1(1)  goal1(2)] then guess k ..
	then have cns: "card ?m \<noteq> 0" using goal1(1) by auto
	moreover have "card ?m < 2"
	proof(rule ccontr)
		case goal1
		obtain a b where ab: "a \<in> ?m" "b \<in> ?m" "a < b" 
		using card2[OF leI[OF goal1]] by blast
		thus False by fastforce
	qed
	ultimately show False using goal1(3) by linarith
qed
lemma select_is_lowest: "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> is_lowest_element (select_lowest S) S"
unfolding is_lowest_element_def
proof -
	case goal1
	note select_set_ov[OF goal1(1) goal1(2)]
	then obtain l where l: "{m \<in> S. \<forall>om\<in>S. m \<le> om} = {l}" by (metis (no_types, lifting) One_nat_def card_eq_SucD)
	thus ?case unfolding select_lowest_def by auto 
qed
lemma finite_ifex_variable_set: "finite (ifex_variable_set k)" by(induction k) simp_all
lemma nonempty_if_variable_set: "ifex_variable_set (IF v t e) \<noteq> {}" by simp
lemma dings_select_helper: "i = (IF iv it ie) \<Longrightarrow> k = (\<Union>(ifex_variable_set ` {i,t,e})) \<Longrightarrow> finite k \<and> k \<noteq> {}"
	using finite_ifex_variable_set nonempty_if_variable_set by auto

fun restrict where
  "restrict (IF v t e) var val = (let rt = restrict t var val; re = restrict e var val in
                   (if v = var then (if val then rt else re) else (IF v rt re)))" |
  "restrict i _ _ = i"

value "ordner (IF 1 Falseif (IF (0::nat) (IF 0 Falseif Falseif) Falseif))"
value "restrict (IF (1::nat) Falseif (IF 0 (IF 0 Falseif Falseif) Falseif)) 1 False"
(* definition "bf2_restrict (i::nat) (val::bool) (func::boolfunc2) \<equiv> (\<lambda>v. func (v(i:=val)))" *)
value "ordner (IF (0::nat) (IF 0 Falseif Falseif) Falseif)"

declare Let_def[simp]

lemma not_element_restrict: "var \<notin> ifex_variable_set (restrict b var val)"
  by (induction b) auto

lemma restrict_assignment: "val_ifex b (ass(var := val)) \<longleftrightarrow> val_ifex (restrict b var val) ass"
  by (induction b) auto

lemma restrict_variables_subset: "ifex_variable_set (restrict b var val) \<subseteq> ifex_variable_set b"
  by (induction b) auto

lemma restrict_ordner_invar: "ordner b \<Longrightarrow> ordner (restrict b var val)"
  using restrict_variables_subset by (induction b) (fastforce)+

lemma restrict_val_invar: "\<forall>ass. a ass = val_ifex b ass \<Longrightarrow> 
      (bf2_restrict var val a) ass = val_ifex (restrict b var val) ass"
  unfolding bf2_restrict_def using restrict_assignment by simp

lemma restrict_ifex_bf2_rel: 
"(a, b) \<in> ifex_bf2_rel \<Longrightarrow> (bf2_restrict var val a, restrict b var val) \<in> ifex_bf2_rel"
  unfolding ifex_bf2_rel_def using restrict_ordner_invar restrict_val_invar
  by (clarsimp simp add: bf2_restrict_def restrict_assignment)

function dings :: "'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> ('a :: linorder) ifex" where
  "dings Trueif t e = t" |
  "dings Falseif t e = e" |
  "dings (IF iv it ie) t e = (let i = (IF iv it ie); x = select_lowest (\<Union>(ifex_variable_set ` {i,t,e})) in 
                         (IF x (dings (restrict i x True) (restrict t x True) (restrict e x True))
                               (dings (restrict i x False) (restrict t x False) (restrict e x False))))"
by pat_completeness auto

lemma restrict_size_le: "size (restrict k x val) \<le> size k"
by(induction k) (auto)
lemma restrict_size_less: "x \<in> ifex_variable_set k \<Longrightarrow> size (restrict k x val) < size k"
proof(induction k)
	case (IF v t e)
	thus ?case
	proof(cases "v = x")
		case True
		show ?thesis by(simp only: True restrict.simps refl if_True) (cases val, simp_all add: preorder_class.le_less_trans[OF restrict_size_le])
	next
		case False note of = this
		show ?thesis
		proof(cases "x \<in> ifex_variable_set t")
			case True
			show ?thesis by(simp only: restrict.simps False if_False ifex.size) (simp add: IF.IH(1)[OF True] restrict_size_le add.commute add_le_less_mono)
		next
			case False
			have *: "x \<in> ifex_variable_set e"
			proof(rule ccontr)
				assume "x \<notin> ifex_variable_set e"
				note this False `v \<noteq> x`
				with IF.prems show False by simp
			qed
			show ?thesis by(simp only: restrict.simps of if_False ifex.size) (simp add: IF.IH(2)[OF *] add_mono_thms_linordered_field(4) restrict_size_le)
		qed
	qed
qed simp_all
lemma restrict_size_eqE: "size k = size (restrict k x val) \<Longrightarrow> x \<notin> ifex_variable_set k"
	using less_not_refl restrict_size_less by metis

lemma termlemma2: "xa = select_lowest (\<Union>(ifex_variable_set ` {(IF iv it ie), t, e})) \<Longrightarrow>
       (size (restrict (IF iv it ie) xa val) + size (restrict t xa val) + size (restrict e xa val)) < (size (IF iv it ie) + size t + size e)"
proof(rule ccontr, unfold not_less)
	case goal1 thus ?case
	proof(cases "size (IF iv it ie) + size t + size e < size (restrict (IF iv it ie) xa val) + size (restrict t xa val) + size (restrict e xa val)")
		case False
		with goal1 have *: "size (IF iv it ie) + size t + size e = size (restrict (IF iv it ie) xa val) + size (restrict t xa val) + size (restrict e xa val)" by auto
		have 1: "size (IF iv it ie) = size (restrict (IF iv it ie) xa val)" using restrict_size_le * by (metis False add_less_le_mono order.not_eq_order_implies_strict)
		have 2: "size t = size (restrict t xa val)" using restrict_size_le * by (metis False add.commute add_less_le_mono order.not_eq_order_implies_strict)
		have 3: "size e = size (restrict e xa val)" using * 1 2 by linarith
		note restrict_size_eqE[OF 1] restrict_size_eqE[OF 2] restrict_size_eqE[OF 3]
		then show False unfolding goal1 using dings_select_helper[OF refl refl] 
			conjunct1[OF select_is_lowest[unfolded is_lowest_element_def], of "(\<Union>(ifex_variable_set ` {(IF iv it ie), t, e}))"] by auto 
	next
		case True thus False using restrict_size_le by (metis add_mono_thms_linordered_semiring(1) leD)
	qed
qed
lemma termlemma: "xa = select_lowest (\<Union>(ifex_variable_set ` {(IF iv it ie), t, e})) \<Longrightarrow>
       (case (restrict (IF iv it ie) xa val, restrict t xa val, restrict e xa val) of (i, t, e) \<Rightarrow> size i + size t + size e) < (case (IF iv it ie, t, e) of (i, t, e) \<Rightarrow> size i + size t + size e)"
using termlemma2 by fast
termination dings by(relation "measure (\<lambda>(i,t,e). size i + size t + size e)", rule wf_measure, unfold in_measure) (simp_all only: termlemma)+

definition "const x _ = x" (* Mehr Haskell wagen *)
lemma rel_true_false: "(a, Trueif) \<in> ifex_bf2_rel \<Longrightarrow> a = const True" "(a, Falseif) \<in> ifex_bf2_rel \<Longrightarrow> a = const False"
	unfolding fun_eq_iff const_def
	unfolding ifex_bf2_rel_def 
	by simp_all
lemma rel_if: "(a, IF v t e) \<in> ifex_bf2_rel \<Longrightarrow> (ta, t) \<in> ifex_bf2_rel \<Longrightarrow> (ea, e) \<in> ifex_bf2_rel \<Longrightarrow> a = (\<lambda>as. if as v then ta as else ea as)"
	unfolding fun_eq_iff const_def
	unfolding ifex_bf2_rel_def 
	by simp_all
lemma "as v \<Longrightarrow> (a, (IF v t e)) \<in> ifex_bf2_rel \<Longrightarrow> (bf2_restrict v True a, t) \<in> ifex_bf2_rel"
unfolding in_rel_def[symmetric]
unfolding ifex_bf2_rel_def
unfolding in_rel_Collect_split_eq
unfolding val_ifex.simps
unfolding ordner.simps
unfolding bf2_restrict_def
oops
lemma ifex_bf2_construct: "(ta, tb) \<in> ifex_bf2_rel \<Longrightarrow> (ea, eb) \<in> ifex_bf2_rel \<Longrightarrow> ordner (IF x tb eb) \<Longrightarrow> (\<lambda>as. if as x then ta as else ea as, IF x tb eb) \<in> ifex_bf2_rel"
	unfolding fun_eq_iff const_def
	unfolding ifex_bf2_rel_def
	by simp
	
lemma ordner_implied: "(a, b) \<in> ifex_bf2_rel \<Longrightarrow> ordner b" unfolding ifex_bf2_rel_def by simp

lemma img_three: "foo ` {a, b, c} = {foo a, foo b, foo c}" by simp
lemma Un_three: "\<Union>{a, b, c} = a \<union> b \<union> c" by auto

lemma single_valued_rel: "single_valued (ifex_bf2_rel\<inverse>)"
	unfolding single_valued_def
	unfolding ifex_bf2_rel_def
	unfolding converse_unfold
	unfolding in_rel_def[symmetric]  in_rel_Collect_split_eq
	by blast

lemma ifex_variable_set_dings_ss: "ifex_variable_set (dings i t e) \<subseteq> \<Union>(ifex_variable_set ` {i, t, e})"
apply(induction i t e rule: dings.induct)
apply simp_all[2]
apply(subst dings.simps)
apply(unfold Let_def)
apply(subst ifex_variable_set.simps)
apply(rule le_supI)
apply(rule le_supI)
apply rule
apply(unfold singleton_iff)
apply(meson dings_select_helper is_lowest_element_def select_is_lowest)
proof -
	case goal1
	show ?case
		apply(rule subset_trans[OF goal1(1)[OF refl refl]])
		apply(unfold img_three)
		using restrict_variables_subset by fastforce
next
	case goal2
	show ?case
		apply(rule subset_trans[OF goal2(2)[OF refl refl]])
		apply(unfold img_three)
		using restrict_variables_subset by fastforce
qed

lemma Let_keeper: "f (let x = a in b x) = (let x = a in f (b x))" by simp
lemma Let_ander: "(let x = a in b x \<and> c x) = ((let x = a in b x) \<and> (let x = a in c x))" by simp
lemma Let2assm: "(\<And>x. x = foo \<Longrightarrow> f x) \<Longrightarrow> let x = foo in f x" by simp

lemma hlp1: "x \<in> \<Union>((\<lambda>vr. ifex_variable_set (restrict vr (select_lowest (\<Union>(ifex_variable_set ` k))) vl)) ` k)
	\<Longrightarrow> select_lowest (\<Union>(ifex_variable_set ` k)) < x"
sorry

lemma order_dings_invar: "ordner i \<Longrightarrow> ordner t \<Longrightarrow> ordner e \<Longrightarrow> ordner (dings i t e)"
	apply(induction i t e rule: dings.induct)
	  apply simp_all[2]
	apply(subst dings.simps)
	apply(unfold Let_keeper)
	apply(subst ordner.simps)
	apply(rule Let2assm)+
	apply rule
	 apply rule
	 apply(unfold Un_iff)
	 apply(erule disjE)
	  apply(drule subsetD[OF ifex_variable_set_dings_ss])
	  apply(subgoal_tac "select_lowest (\<Union>(ifex_variable_set ` {x, t, e})) < xb")
	   apply fast
	  apply(rule hlp1)
	  apply blast
	 apply(subgoal_tac "select_lowest (\<Union>(ifex_variable_set ` {x, t, e})) < xb")
	  apply fast
	 apply(rule hlp1[where vl=False])
	 apply(drule subsetD[OF ifex_variable_set_dings_ss])
	 apply blast
	apply(meson restrict_ordner_invar)
done

lemma "
	(ia, ib) \<in> ifex_bf2_rel \<Longrightarrow>
	(ta, tb) \<in> ifex_bf2_rel \<Longrightarrow>
	(ea, eb) \<in> ifex_bf2_rel \<Longrightarrow>
	(bf_ite ia ta ea, dings ib tb eb) \<in> ifex_bf2_rel"
proof(induction ib tb eb arbitrary: ia ta ea rule: dings.induct)
	case goal3 note goal1 = goal3
	let ?strtr = "select_lowest (\<Union>(ifex_variable_set ` {IF iv it ie, t, e}))"
	have mrdr: "ordner (IF ?strtr (dings (restrict (IF iv it ie) ?strtr True) (restrict t ?strtr True) (restrict e ?strtr True))
                                  (dings (restrict (IF iv it ie) ?strtr False) (restrict t ?strtr False) (restrict e ?strtr False)))"
		unfolding ordner.simps
		by(rule conjI, rule, unfold Un_iff, erule disjE)
		    (((drule subsetD[OF ifex_variable_set_dings_ss], 
			unfold img_three, meson hlp1[where k = "{IF iv it ie, t, e}", unfolded img_three])+),
			metis restrict_ordner_invar order_dings_invar ordner_implied goal1(3,4,5))
    have kll: "(\<lambda>as. if as ?strtr then bf_ite (bf2_restrict ?strtr True ia) (bf2_restrict ?strtr True ta) (bf2_restrict ?strtr True ea) as
                                   else bf_ite (bf2_restrict ?strtr False ia) (bf2_restrict ?strtr False ta) (bf2_restrict ?strtr False ea) as) 
               = bf_ite ia ta ea"
               unfolding bf_ite_def bf2_restrict_def fun_eq_iff
               by(simp add: fun_upd_idem)+
	note (* free the induction hypotheses *)  
		goal1(1)[OF refl refl restrict_ifex_bf2_rel[OF goal1(3)] restrict_ifex_bf2_rel[OF goal1(4)] restrict_ifex_bf2_rel [OF goal1(5)]]
		goal1(2)[OF refl refl restrict_ifex_bf2_rel[OF goal1(3)] restrict_ifex_bf2_rel[OF goal1(4)] restrict_ifex_bf2_rel [OF goal1(5)]]
	note ifex_bf2_construct(* this is basically the central property *)[OF this mrdr] 
	thus ?case unfolding dings.simps Let_def kll by blast
qed (frule rel_true_false, simp only: dings.simps bf_ite_def const_def if_True if_False)+

fun restrict_top :: "('a :: linorder) ifex \<Rightarrow> bool \<Rightarrow> 'a ifex" where
  "restrict_top (IF v t e) val = (if val then t else e)" |
  "restrict_top i _ = i"
  
lemma restrict_untouched_id: "x \<notin> ifex_variable_set t \<Longrightarrow> restrict t x val = t" (* umkehrung gilt auch\<dots> *)
proof(induction t)
	case (IF v t e)
	from IF.prems have "x \<notin> ifex_variable_set t" "x \<notin> ifex_variable_set e" by auto
	note mIH = IF.IH(1)[OF this(1)] IF.IH(2)[OF this(2)]
	from IF.prems have "x \<noteq> v" by simp
	thus ?case unfolding restrict.simps Let_def mIH  by simp
qed simp_all

lemma "ordner (IF v t e) \<Longrightarrow> restrict (IF v t e) v val = restrict_top (IF v t e) val"
	using restrict_untouched_id by fastforce (* fastforce ftw *)


(* INDUCTIVE DEFINITION *)

inductive ind_ite :: "('a::linorder) ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> bool" where
ind_ite_true:   "ind_ite t Trueif t e" |
ind_ite_false:  "ind_ite e Falseif t e" |
ind_ite_if:     "x \<in> (ifex_variable_set i \<union> ifex_variable_set t \<union> ifex_variable_set e) \<Longrightarrow>
   \<forall>v \<in> (ifex_variable_set i \<union> ifex_variable_set t \<union> ifex_variable_set e). x \<le> v \<Longrightarrow>
   i = IF iv tv ev \<Longrightarrow>
   ind_ite l (restrict i x True) (restrict t x True) (restrict e x True) \<Longrightarrow>
   ind_ite r (restrict i x False) (restrict t x False) (restrict e x False) \<Longrightarrow>
   ind_ite (IF x l r) i t e"

lemma "ind_ite b i t e \<longleftrightarrow> dings i t e = b"
 (* proven by nitpick finding nothing *)
  oops 

lemma "ifex_variable_set i \<union> ifex_variable_set t \<union> ifex_variable_set e =
       \<Union>(ifex_variable_set ` {i,t,e})"
  by blast

lemma "ind_ite Falseif Trueif Falseif Trueif" apply(rule ind_ite_true) done

lemma "ind_ite (IF 1 (IF 2 Falseif Trueif) Trueif) 
              (IF (1::nat) (IF 2 Trueif Falseif) Falseif) (Falseif) (Trueif)"
  apply(rule) apply(force) apply(auto) apply(rule) apply(auto) using ind_ite.intros apply(auto) done

value "dings (IF (1::nat) (IF 2 Trueif Falseif) Falseif) (Falseif) (Trueif)"

lemma ind_ite_variables_subset: "ind_ite b i t e \<Longrightarrow> 
  ifex_variable_set b \<subseteq> ifex_variable_set i \<union> ifex_variable_set t \<union> ifex_variable_set e"
  proof(induction rule: ind_ite.induct)
  case(ind_ite_if x i t e iv tv ev l r) 
    from this(6,7) have 
         "ifex_variable_set (IF x l r) = {x} \<union> ifex_variable_set l \<union> ifex_variable_set r"
         "ifex_variable_set l \<subseteq> ifex_variable_set i \<union> ifex_variable_set t \<union> ifex_variable_set e"
         "ifex_variable_set r \<subseteq> ifex_variable_set i \<union> ifex_variable_set t \<union> ifex_variable_set e"
        using restrict_variables_subset[of i x True] restrict_variables_subset[of t x True] 
              restrict_variables_subset[of e x True] restrict_variables_subset[of i x False]
              restrict_variables_subset[of t x False] restrict_variables_subset[of e x False]
        by auto
     with ind_ite_if(1) show ?case by simp
qed (auto)


end

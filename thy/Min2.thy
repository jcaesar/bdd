theory Min2
imports Main
begin

(* this is basically legacy stuff as we could just replace select_lowest by Min. 
   However, I think that would require tainting our type with the sort class.
   This requires only linorder. *) 

(* had we done ifex_variable_list instead of _set, we would have gotten out way easier\<dots> *)
definition "is_lowest_element e S = (e \<in> S \<and> (\<forall>oe \<in> S. e \<le> oe))"
definition select_lowest :: "'a set \<Rightarrow> 'a :: linorder" where "select_lowest a = the_elem {m. m \<in> a \<and> (\<forall>om \<in> a. m \<le> om)}"
lemma select_hlp_ex: "finite (S :: ('a :: linorder) set)  \<Longrightarrow> S \<noteq> {} \<Longrightarrow> \<exists>k. k \<in> {m. m \<in> S \<and> (\<forall>om \<in> S. m \<le> om)}"
using Min.coboundedI Min_in mem_Collect_eq by blast
lemma card2_ordered_pair: "2 \<le> card (S :: ('a :: linorder) set) \<Longrightarrow> \<exists>a b. a \<in> S \<and> b \<in> S \<and> a < b"
proof -
	assume "2 \<le> card S"
	then obtain k where a: "card S = Suc (Suc k)" using Nat.le_iff_add by auto
	from card_eq_SucD[OF this]    obtain a B  where aB: "S = insert a B"  "a \<notin> B"  "card B = Suc k" by blast
	from card_eq_SucD[OF this(3)] obtain b B' where bB: "B = insert b B'" "b \<notin> B'" "card B' = k"    by blast
	have "a \<noteq> b" using aB(2) bB(1) by simp
	moreover have "a \<in> S" "b \<in> S" using aB(1) bB(1) by simp_all
	ultimately show ?thesis using aB(1) bB(1) by(meson neq_iff)
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
		using card2_ordered_pair[OF leI[OF goal1]] by blast
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
(* Yes, this is the same as Min. *)
lemma "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> Min S = select_lowest S"
	by (meson Min_eqI is_lowest_element_def select_is_lowest)
	
end
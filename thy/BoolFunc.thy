theory BoolFunc
imports Main
begin

type_synonym boolfunc = "bool list \<Rightarrow> bool"

find_consts "'a list \<Rightarrow> nat \<Rightarrow> 'a"

definition "bf_and01 \<equiv> (\<lambda>l. l ! 0 \<and> l ! 1)"
definition "bf_or01 \<equiv> (\<lambda>l. l ! 0 \<or> l ! 1)"
definition "bf_True \<equiv> (\<lambda>l. True)"
definition "bf_False \<equiv> (\<lambda>l. False)"

definition "bf_ite i t e \<equiv> (\<lambda>l. if i l then t l else e l)"
definition "bf_and a b \<equiv> bf_ite a b bf_False"
definition "bf_or a b \<equiv> bf_ite a bf_True b"
definition "bf_not b \<equiv> bf_ite b bf_False bf_True"

lemma "bf_and (bf_not a) (bf_not b) = bf_not (bf_or a b)" (* test *)
	unfolding bf_and_def bf_or_def bf_not_def bf_ite_def bf_True_def bf_False_def
	by meson
	
definition "bf_ithvar i \<equiv> (\<lambda>l. l ! i) :: boolfunc"

value "bf_and (bf_not (bf_ithvar 2)) (bf_or (bf_ithvar 1) (bf_ithvar 0)) [False, True, False]"

(* Not all operations can be implemented with one ITE, some require a not. *)
definition "bf_xor a b \<equiv> bf_ite a (bf_not b) b"
definition "bf_bipl a b \<equiv> bf_ite a b (bf_not b)"

(* Just some fun with Shannon, for the sake of Brace90's Section 4.4. *)
type_synonym 'a boolfunc2 = "('a \<Rightarrow> bool) \<Rightarrow> bool"
definition "bf2_ithvar i \<equiv> (\<lambda>v. v i) :: 'a boolfunc2"
definition "bf2_restrict (i::'a) (val::bool) (func::'a boolfunc2) \<equiv> (\<lambda>v. func (v(i:=val)))"
definition "bf2_decompose f i \<equiv> bf_or (bf_and (bf2_restrict i True f) (bf2_ithvar i)) 
                                      (bf_and (bf2_restrict i False f) (bf_not (bf2_ithvar i)))"
lemma shannon_decomposition: "bf2_decompose f i = f"
	unfolding fun_eq_iff
	unfolding bf2_decompose_def bf2_restrict_def bf2_ithvar_def
	unfolding bf_or_def bf_and_def bf_not_def bf_ite_def bf_True_def bf_False_def
	(* try an apply auto here if you want to see why *)
	by(simp add: fun_upd_idem)

(* so technically, boolfunc2 is abstract and boolfunc is an implementation? Or is it the other way? *)
value "upt 3 10"
definition abstract_bf_bf2 :: "nat \<Rightarrow> boolfunc \<Rightarrow> nat boolfunc2"
where "abstract_bf_bf2 arity bf v = bf (map v (upt 0 arity))"
definition concretize_bf2_bf :: "nat boolfunc2 \<Rightarrow> boolfunc"
where "concretize_bf2_bf bf l = bf (\<lambda>i. l ! i)"
lemma "concretize_bf2_bf (abstract_bf_bf2 (length l) bf) l = bf l"
	unfolding abstract_bf_bf2_def concretize_bf2_bf_def
	by (simp add: map_nth)
(* trying one of those equivalence proofs, just the wrong way around. (This one is too easy though.) *)
lemma "bf_ite (concretize_bf2_bf bf1) (concretize_bf2_bf bf2) (concretize_bf2_bf bf3) = concretize_bf2_bf (bf_ite bf1 bf2 bf3)"
	unfolding fun_eq_iff
	unfolding bf_ite_def concretize_bf2_bf_def
	by clarify

(* Some more Brace90's Section 4.4: This is basically how to recursively implement ite *)
lemma brace90shannon:
	assumes "Z = bf_ite F G H"
	shows "Z = bf_ite (bf2_ithvar i) 
	                  (bf_ite (bf2_restrict i True F) (bf2_restrict i True G) (bf2_restrict i True H))
	                  (bf_ite (bf2_restrict i False F) (bf2_restrict i False G) (bf2_restrict i False H))"
	using assms
	unfolding fun_eq_iff
	unfolding bf2_decompose_def bf2_restrict_def bf2_ithvar_def
	unfolding bf_or_def bf_and_def bf_not_def bf_ite_def bf_True_def bf_False_def
	by(simp_all add: fun_upd_idem)

lemma brace90shannon2: "bf_ite F G H ass = bf_ite (bf2_ithvar i) 
	                  (bf_ite (bf2_restrict i True F) (bf2_restrict i True G) (bf2_restrict i True H))
	                  (bf_ite (bf2_restrict i False F) (bf2_restrict i False G) (bf2_restrict i False H)) ass"
using brace90shannon by metis
	

end
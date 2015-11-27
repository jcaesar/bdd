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
  "ordner (IF v t e) = ((\<forall>tv \<in> ifex_variable_set t. v < tv) \<and> (\<forall>ev \<in> ifex_variable_set t. v < ev)
                       \<and> ordner t \<and> ordner e)" |
  "ordner Trueif = True" |
  "ordner Falseif = True"


definition ifex_bf2_rel where
  "ifex_bf2_rel = {(a,b) | a b. (\<forall>ass. a ass \<longleftrightarrow> val_ifex b ass)  \<and> ordner b}"

definition select where "select a = undefined"

fun restrict where
  "restrict (IF v t e) var val = (let rt = restrict t var val; re = restrict e var val in
                   (if v = var then (if val then rt else re) else (IF v rt re)))" |
  "restrict i _ _ = i"
  
value "ordner (IF 1 Falseif (IF (0::nat) (IF 0 Falseif Falseif) Falseif))"
value "restrict (IF (1::nat) Falseif (IF 0 (IF 0 Falseif Falseif) Falseif)) 1 False"
(* definition "bf2_restrict (i::nat) (val::bool) (func::boolfunc2) \<equiv> (\<lambda>v. func (v(i:=val)))" *)
value "ordner (IF (0::nat) (IF 0 Falseif Falseif) Falseif)"

lemma "(a, b) \<in> ifex_bf2_rel \<Longrightarrow> restrict b var val = b' \<Longrightarrow> bf2_restrict var val a = a' \<Longrightarrow> (a', b') \<in> ifex_bf2_rel"
  unfolding ifex_bf2_rel_def 
oops

function dings :: "'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex" where
  "dings Trueif t e = t" |
  "dings Falseif t e = e" |
  "dings (IF iv it ie) t e = (let i = (IF iv it ie); x = select (ifex_variable_set ` {i,t,e}) in 
                         (IF x (dings (restrict i x True) (restrict t x True) (restrict e x True))
                               (dings (restrict i x False) (restrict t x False) (restrict e x False))))"
by pat_completeness auto

lemma restrict_size_le: "size (restrict k x val) \<le> size k"
by(induction k) (simp_all, force)
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

termination dings
apply(relation "measure size", rule wf_measure)


end
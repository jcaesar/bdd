theory AbstractBDD
imports BoolFunc
begin

datatype nodelabel = LabeledNode nat | DTrue | DFalse 
record abdd_node =
	var :: nat
	label :: nodelabel
	right :: nodelabel
	left :: nodelabel
	
record abdd =
	nodes :: "abdd_node set"
	start :: nodelabel

definition abdd_reference_integrity :: "abdd \<Rightarrow> bool" where
"abdd_reference_integrity b \<equiv> (\<forall>n \<in> nodes b.
	(\<forall>m \<in> nodes b. (label m = label n) \<longrightarrow> (m = n)) \<and> (
	case (label n) of 
		LabeledNode _ \<Rightarrow> ((\<exists>l \<in> nodes b. label l = left n) \<and> (\<exists>l \<in> nodes b. label l = right n)) |
		_ \<Rightarrow> True))"

definition "abddn_is_child c n \<equiv> (label c = left n \<or> label c = right n)" 
inductive abdd_reachable :: "abdd \<Rightarrow> abdd_node \<Rightarrow> abdd_node \<Rightarrow> bool" where
ar_base: "ln2 \<in> nodes bdd \<Longrightarrow> abddn_is_child ln2 ln  \<Longrightarrow> abdd_reachable bdd ln ln2" |
ar_step: "ln2 \<in> nodes bdd \<Longrightarrow> abdd_reachable bdd ln ln2 \<Longrightarrow> abddn_is_child ln3 ln2  \<Longrightarrow> abdd_reachable bdd ln ln3"
definition "abdd_reachable_set bdd node = {n |n. abdd_reachable bdd node n}"

definition abdd_is_dag :: "abdd \<Rightarrow> bool" where
"abdd_is_dag bdd = (\<forall>n \<in> nodes bdd. \<not>abdd_reachable bdd n n)"

definition "getnode bdd lbl \<equiv> THE node. node \<in> nodes bdd \<and> label node = lbl"
lemma "abdd_reference_integrity bdd \<Longrightarrow> node \<in> nodes bdd \<Longrightarrow>
	(case label node of LabeledNode _ \<Rightarrow> True | _ \<Rightarrow> False) \<Longrightarrow> getnode bdd (right node) \<in> nodes bdd"
unfolding abdd_reference_integrity_def getnode_def
apply(cases "label node") defer apply auto[2]
apply clarsimp
apply(rule the1I2) defer apply simp
find_theorems "\<exists>!x . _"
apply(rule ex1I)
thm ex1I
oops

function abstract_abdd_hlp :: "abdd \<Rightarrow> abdd_node \<Rightarrow> boolfunc" where
"abstract_abdd_hlp bdd node l = (if (abdd_is_dag bdd \<and> abdd_reference_integrity bdd)
	then (if l ! var node 
		then abstract_abdd_hlp bdd (getnode bdd (right node)) l 
		else abstract_abdd_hlp bdd (getnode bdd (left node)) l)
	else undefined)"
by pat_completeness auto

lemma "abdd_is_dag bdd \<Longrightarrow>
       (*abdd_reference_integrity bdd \<Longrightarrow>*) 
       abdd_reachable_set bdd (getnode bdd (right node)) \<subseteq> (abdd_reachable_set bdd node)"
apply(rule, unfold abdd_reachable_set_def, simp) oops

termination abstract_abdd_hlp
apply(relation "measure (card \<circ> (\<lambda>(bdd,node,_). abdd_reachable_set bdd node))", rule wf_measure, unfold in_measure comp_def)
(*apply(unfold getnode_def abdd_reference_integrity_def abdd_reachable_set_def)*)
apply clarsimp
apply(rule psubset_card_mono) defer
apply(rule, rule, unfold abdd_reachable_set_def, simp)[1]
oops



end
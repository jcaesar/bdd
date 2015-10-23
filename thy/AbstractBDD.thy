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

definition abdd_reference_integrity_set :: "abdd \<Rightarrow> bool" where
"abdd_reference_integrity_set b \<equiv> (\<forall>n \<in> nodes b.
	(\<forall>m \<in> nodes b. (label m = label n) \<longrightarrow> (m = n)) \<and> (
	case (label n) of 
		LabeledNode _ \<Rightarrow> ((\<exists>l \<in> nodes b. label l = left n) \<and> (\<exists>l \<in> nodes b. label l = right n)) |
		_ \<Rightarrow> True))"
definition "abdd_collect_refs bdd = {start bdd} \<union> right ` nodes bdd \<union> left ` nodes bdd"
definition abdd_reference_integrity :: "abdd \<Rightarrow> bool" where
	"abdd_reference_integrity bdd \<equiv> (\<forall>lb \<in> abdd_collect_refs bdd. \<exists>node \<in> nodes bdd. label node = lb)"
definition abdd_nodes_unique :: "abdd \<Rightarrow> bool" where
	"abdd_nodes_unique bdd \<equiv> (\<forall>n \<in> nodes bdd. (\<forall>m \<in> nodes bdd. (label m = label n) \<longrightarrow> (m = n)))"
		
definition "abddn_is_child c n \<equiv> (label c = left n \<or> label c = right n)" 
inductive abdd_reachable :: "abdd \<Rightarrow> abdd_node \<Rightarrow> abdd_node \<Rightarrow> bool" where
ar_base: "ln2 \<in> nodes bdd \<Longrightarrow> abddn_is_child ln2 ln  \<Longrightarrow> abdd_reachable bdd ln ln2" |
ar_step: "ln2 \<in> nodes bdd \<Longrightarrow> abdd_reachable bdd ln ln2 \<Longrightarrow> abddn_is_child ln3 ln2  \<Longrightarrow> abdd_reachable bdd ln ln3"
code_pred abdd_reachable .
definition "abdd_reachable_set bdd node = {n |n. abdd_reachable bdd node n}"
definition "abdd_cycle_free bdd = (\<forall>node \<in> nodes bdd. \<not> abdd_reachable bdd node node)"

definition abdd_is_dag :: "abdd \<Rightarrow> bool" where
"abdd_is_dag bdd = (\<forall>n \<in> nodes bdd. \<not>abdd_reachable bdd n n)"

lemma "abdd_is_dag bdd \<Longrightarrow>
       (*abdd_reference_integrity bdd \<Longrightarrow>*) 
       abdd_reachable_set bdd (getnode bdd (right node)) \<subseteq> (abdd_reachable_set bdd node)"
apply(rule, unfold abdd_reachable_set_def, simp)
oops

definition "abdd_terminal state = (case state of LabeledNode _ \<Rightarrow> False | _ \<Rightarrow> True)" 

inductive abdd_smallstep  where
start: "abdd_smallstep bdd assignment (start bdd)" |
step[elim]: "abdd_smallstep bdd assignment state \<Longrightarrow> \<not> abdd_terminal state \<Longrightarrow> node \<in> nodes bdd \<Longrightarrow> label node = state \<Longrightarrow> abdd_smallstep bdd assignment ((if assignment ! var node then right else left) node)"
print_theorems
code_pred abdd_smallstep .
inductive abdd_smallstep2  where
start: "abdd_smallstep2 bdd assignment (start bdd)" |
stepright: "abdd_smallstep2 bdd assignment state \<Longrightarrow> \<not> abdd_terminal state \<Longrightarrow> node \<in> nodes bdd \<Longrightarrow> label node = state \<Longrightarrow> assignment ! var node \<Longrightarrow> abdd_smallstep2 bdd assignment (right node)" |
stepleft: "abdd_smallstep2 bdd assignment state \<Longrightarrow> \<not> abdd_terminal state \<Longrightarrow> node \<in> nodes bdd \<Longrightarrow> label node = state \<Longrightarrow> \<not>assignment ! var node \<Longrightarrow> abdd_smallstep2 bdd assignment (left node)"
lemma abdd_smallstep_2_eq: "abdd_smallstep bdd ass state = abdd_smallstep2 bdd ass state"
	apply(rule)
	 apply(induction rule: abdd_smallstep.induct)
	  apply(simp add: abdd_smallstep2.start)
	 apply(force dest: abdd_smallstep2.stepright abdd_smallstep2.stepleft)
	apply(induction rule: abdd_smallstep2.induct)
	  apply(simp add: abdd_smallstep.start)
	 apply(force dest: abdd_smallstep.step)
	apply(force dest: abdd_smallstep.step)
done

definition "abdd_xor \<equiv> \<lparr> nodes = {
	\<lparr> var = 0, label = LabeledNode 5, right = LabeledNode 4 , left = LabeledNode 3 \<rparr>,
	\<lparr> var = 1, label = LabeledNode 4, right = DFalse , left = DTrue \<rparr>,
	\<lparr> var = 1, label = LabeledNode 3, right = DTrue , left = DFalse \<rparr>,
	\<lparr> var = 0, label = DTrue , right = DTrue , left = DTrue \<rparr>,
	\<lparr> var = 0, label = DFalse , right = DFalse , left = DFalse \<rparr>
}, start = LabeledNode 5\<rparr>"

lemma "abdd_reference_integrity abdd_xor" by eval
lemma "abdd_cycle_free abdd_xor" unfolding abdd_cycle_free_def apply(subst abdd_xor_def, simp) apply(rule) oops 
lemma "abdd_smallstep abdd_xor [False, True] DTrue" 
proof -
	have 1: "abdd_smallstep abdd_xor [False, True] (start abdd_xor)" by(simp add: abdd_smallstep.start)
	have 2: "\<lparr> var = 0, label = LabeledNode 5, right = LabeledNode 4 , left = LabeledNode 3 \<rparr> \<in> nodes abdd_xor" by(simp add: abdd_xor_def)
	have 3: "abdd_smallstep abdd_xor [False, True] (LabeledNode 3)" using abdd_smallstep.step[OF 1 _ 2] by(simp add: abdd_xor_def abdd_terminal_def)
	have 4: "\<lparr> var = 1, label = LabeledNode 3, right = DTrue , left = DFalse \<rparr> \<in> nodes abdd_xor" by(simp add: abdd_xor_def)
	show 5: "abdd_smallstep abdd_xor [False, True] DTrue" using abdd_smallstep.step[OF 3 _ 4] by(simp add: abdd_xor_def abdd_terminal_def)
qed (* So how do I do this automatically? *)
values "{t|t. abdd_smallstep2 abdd_xor [False, True] t}" (* I guess I don't? *)

definition "abstract_abdd1 bdd ass = (
	if abdd_smallstep bdd ass DTrue
		then Some True else (
	if abdd_smallstep bdd ass DFalse
		then Some False
	else None))"

lemma abdd_steppable_ind: " (\<exists>node \<in> nodes bdd. label node = state)
	\<Longrightarrow> abdd_smallstep bdd ass state \<Longrightarrow> (\<exists>nextnode \<in> nodes bdd. abdd_smallstep bdd ass (label nextnode))" by blast


lemma "abdd_reference_integrity bdd \<Longrightarrow> abdd_cycle_free bdd \<Longrightarrow> abstract_abdd1 bdd ass \<noteq> None"
apply(unfold abstract_abdd1_def)
apply(unfold abdd_smallstep_2_eq)
oops


end

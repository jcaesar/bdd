theory TestImpl1
imports Abstract_Impl
begin

record bdd = 
	nodes :: "nat \<Rightarrow> (nat \<times> nat \<times> nat)"
	max :: nat

fun destrmi :: "nat \<Rightarrow> bdd \<Rightarrow> (nat, nat) IFEXD" where
"destrmi 0 bdd = FD" |
"destrmi (Suc 0) bdd = TD" |
"destrmi n bdd = (case nodes bdd n of (v, t, e) \<Rightarrow> IFD v t e)"

fun tmi where "tmi bdd = (1, \<lparr>nodes = nodes bdd, max = min 2 (max bdd)\<rparr>)"
fun fmi where "fmi bdd = (1, \<lparr>nodes = nodes bdd, max = min 2 (max bdd)\<rparr>)"
fun ifmi :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bdd \<Rightarrow> (nat \<times> bdd)" where
"ifmi v t e bdd = 
(case List.find (\<lambda>(_,(n,_,_)). v = n) (map (\<lambda>i. (i, nodes bdd i)) (upt 2 (max bdd))) of 
	Some (i,_) \<Rightarrow> (i, bdd) |
	None \<Rightarrow> (max bdd, \<lparr>nodes = (nodes bdd)(max bdd := (v,t,e)), max = Suc (max bdd)\<rparr>))"

fun Rmi_g :: "nat \<Rightarrow> nat ifex \<Rightarrow> bdd \<Rightarrow> bool" where
"Rmi_g (Suc 0) Trueif _ = True" |
"Rmi_g 0 Falseif _ = True" |
"Rmi_g n (IF v t e) bdd = (case nodes bdd n of (nv, nt, ne) \<Rightarrow> nv = v \<and> Rmi_g nt t bdd \<and> Rmi_g ne e bdd)" |
"Rmi_g _ _ _ = False"

interpretation bdd_impl where
	"R s = {(a,b). Rmi_g a b s}" and
	"Timpl s = tmi s" and
	"Fimpl = undefined" and
	"IFimpl = undefined"
	(*"DESTRimpl = destrmi"*)
proof -
	
end
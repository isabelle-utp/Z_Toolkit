theory Set_Toolkit
  imports FSet_Extra "HOL-Library.Adhoc_Overloading"
begin

text \<open> The majority of the Z set toolkit is implemented in the core libraries of HOL. We could
  prove all the axioms of ISO 13568 as theorems, but we omit this for now. The main thing we
  need is to map between finite sets and the normal set type. \<close>

declare [[coercion_enabled]]

subsection \<open> Notation for types as sets \<close>

definition "TUNIV (a::'a itself) = (UNIV :: 'a set)"

syntax "_tvar" :: "type \<Rightarrow> logic" ("[_]\<^sub>T")
translations "['a]\<^sub>T" == "CONST TUNIV TYPE('a)"

lemma TUNIV_mem [simp]: "x \<in> ['a]\<^sub>T"
  by (simp add: TUNIV_def)

end
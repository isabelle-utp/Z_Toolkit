section \<open> Functions \<close>

theory Function_Toolkit
  imports Relation_Toolkit
begin

subsection \<open> Partial Functions \<close>

lemma partial_functions: "X \<rightarrow>\<^sub>p Y = {f \<in> X \<leftrightarrow> Y. \<forall> p \<in> f. \<forall> q \<in> f. p.1 = q.1 \<longrightarrow> p.2 = q.2}"
  by (auto simp add: rel_pfun_def single_valued_def)

end
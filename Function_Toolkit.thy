section \<open> Function Toolkit \<close>

theory Function_Toolkit
  imports Relation_Toolkit
begin

subsection \<open> Partial Functions \<close>

lemma partial_functions: "X \<rightarrow>\<^sub>p Y = {f \<in> X \<leftrightarrow> Y. \<forall> p \<in> f. \<forall> q \<in> f. p.1 = q.1 \<longrightarrow> p.2 = q.2}"
  by (auto simp add: rel_pfun_def single_valued_def)

notation size ("#_" [999] 999)

instantiation set :: (type) size
begin
definition [simp]: "size A = card A"
instance ..
end

instantiation pfun :: (type, type) size
begin

definition size_pfun :: "('a \<Zpfun> 'b) \<Rightarrow> nat" where
"size_pfun f = card (pfun_graph f)"

instance ..

end

lemma size_finite_pfun: "finite (pdom f) \<Longrightarrow> #f = #(dom f)"
  by (simp add: card_pfun_graph size_pfun_def)

subsection \<open> Total Functions \<close>

text \<open> One issue that emerges in this encoding is the treatment of total functions. In Z, a total
  function is a particular kind of partial function whose domain covers the type universe. In HOL,
  a total function is one of the basic types. Typically, one wishes to apply total functions, 
  partial functions, and finite functions to values using the notation @{term "f x"}. In order
  to implement this, we need to coerce the given function @{term f} to a total function, since
  this is fundamental to HOL's application construct. However, that means that we can't also
  coerce a total function to a partial function, as expected by Z, since this would lead to
  a cycle. Consequently, we actually need to create a new ``total function'' type, different
  to the HOL one, to break the cycle. We therefore consider the HOL total function type
  to be meta-logical with respect to Z.  \<close>

declare [[coercion pfun_of_tfun]]

subsection \<open> Disjointness \<close>

consts 
  disjoint :: "'f \<Rightarrow> bool"

adhoc_overloading 
  disjoint rel_disjoint and
  disjoint pfun_disjoint and 
  disjoint list_disjoint 

subsection \<open> Partitions \<close>

consts partitions :: "'f \<Rightarrow> 'a set \<Rightarrow> bool" (infix "partitions" 65)

adhoc_overloading
  partitions rel_partitions and
  partitions pfun_partitions and
  partitions list_partitions

end
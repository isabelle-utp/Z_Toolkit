section \<open> Polymorphic Overriding Operator \<close>

theory Overriding
  imports Relation_Lib
begin

text \<open> We here use type classes to create the overriding operator and instantiate it for relations,
  partial function, and finite functions. Probably this should be better integrated with those
  respective theories in the future. \<close>

class oplus = 
  fixes oplus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 65)

text \<open> FIXME: We should be using Partial Abelian Monoids here ... \<close>

class override = oplus + zero +
  assumes override_idem [simp]: "P \<oplus> P = P"
  and override_assoc: "P \<oplus> (Q \<oplus> R) = (P \<oplus> Q) \<oplus> R"
  and override_lzero [simp]: "0 \<oplus> P = P"
  and override_rzero [simp]: "P \<oplus> 0 = P"

text \<open> We employ some type class trickery to enable a polymorphic operator for override that can
  instantiate @{typ "'a set"}, which is needed for relational overriding. The following class's
  sole purpose is to allow pairs to be the only valid instantiation element for the set type. \<close>

class restrict = 
  fixes res :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  assumes res_idem: "res P P = P"
  and res_assoc: "res P (res Q R) = res (res P Q) R"
  and res_lzero: "res {} P = P"
  and res_rzero: "res P {} = P"

instantiation prod :: (type, type) restrict
begin
definition res_prod :: "('a \<leftrightarrow> 'b) \<Rightarrow> ('a \<leftrightarrow> 'b) \<Rightarrow> 'a \<leftrightarrow> 'b" where [simp]: "res_prod = (+\<^sub>r)"

instance by (intro_classes, simp_all add: rel_override_monoid.add_assoc)
end

instantiation set :: (type) zero
begin

definition zero_set :: "'a set" where
[simp]: "zero_set = {}"

instance ..
end

instantiation set :: (restrict) override
begin
definition oplus_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"oplus_set = res"
instance by (intro_classes, simp_all add: oplus_set_def res_idem res_assoc res_lzero res_rzero)
end

instantiation pfun :: (type, type) override
begin
definition oplus_pfun :: "('a \<Rightarrow>\<^sub>p 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>p 'b) \<Rightarrow> 'a \<Rightarrow>\<^sub>p 'b" where [simp]: "oplus_pfun = (+)"
instance by (intro_classes, simp_all add: add.assoc)
end

instantiation ffun :: (type, type) override
begin
definition oplus_ffun :: "('a \<Zffun> 'b) \<Rightarrow> ('a \<Zffun> 'b) \<Rightarrow> 'a \<Zffun> 'b" where [simp]: "oplus_ffun = (+)"
instance by (intro_classes, simp_all add: add.assoc)
end

end
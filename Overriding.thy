section \<open> Polymorphic Overriding Operator \<close>

theory Overriding
  imports Main
begin

text \<open> We here use type classes to create the overriding operator and instantiate it for relations,
  partial function, and finite functions. \<close>

class oplus = 
  fixes oplus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 65)

class compatible = zero +
  fixes compatible :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "##" 60)
  assumes compatible_sym: "x ## y \<Longrightarrow> y ## x"
  and compatible_zero [simp]: "x ## 0"

class override = oplus + zero + compatible +
  assumes override_idem [simp]: "P \<oplus> P = P"
  and override_assoc: "P \<oplus> (Q \<oplus> R) = (P \<oplus> Q) \<oplus> R"
  and override_lzero [simp]: "0 \<oplus> P = P"
  and override_rzero [simp]: "P \<oplus> 0 = P"
  and override_comm: "P ## Q \<Longrightarrow> P \<oplus> Q = Q \<oplus> P" 

end
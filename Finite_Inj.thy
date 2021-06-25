subsection \<open> Finite Injections \<close>

theory Finite_Inj
  imports Partial_Inj Finite_Fun
begin

typedef ('a, 'b) finj = "{f :: 'a \<Zpinj> 'b. finite(pidom(f))}"
  morphisms pinj_of_finj finj_of_pinj
  by (rule_tac x="{}\<^sub>\<rho>" in exI, simp)

setup_lifting type_definition_finj

type_notation finj (infixr "\<Zfinj>" 1)

end
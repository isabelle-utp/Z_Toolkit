section \<open> Relation Toolkit \<close>

theory Relation_Toolkit
  imports Set_Toolkit
begin

subsection \<open> Conversions \<close>

text \<open> The majority of the relation toolkit is also part of HOL. We just need to generalise
  some of the syntax. \<close>

declare [[coercion rel_apply]]
declare [[coercion pfun_app]]
declare [[coercion pfun_of]]
declare [[coercion pfun_graph]]

subsection \<open> First component projection \<close>

abbreviation (input) "first \<equiv> fst"
notation first ("_.1" [999] 999)

subsection \<open> Second component projection \<close>

abbreviation (input) "second \<equiv> snd"
notation second ("_.2" [999] 999)

subsection \<open> Maplet \<close>

subsection \<open> Domain \<close>

hide_const (open) dom
abbreviation (input) "dom \<equiv> Domain"

subsection \<open> Range \<close>

hide_const (open) ran
abbreviation (input) "ran \<equiv> Range"

subsection \<open> Identity relation \<close>

notation Id_on ("id[_]")

subsection \<open> Relational composition \<close>

notation relcomp (infixr "\<^bold>;" 75)

subsection \<open> Functional composition \<close>

text \<open> We take the liberty of assuming that if a function composition is being applied, then
  probably we want to compose two partial functions, rather than two relations. This makes sense,
  given that relational composition and functional composition are semantically identical 
  (but reversed). \<close>

no_notation comp (infixl "\<circ>" 55)
notation pfun_comp (infixl "\<circ>" 55)

subsection \<open> Domain restriction \<close>

consts dom_res :: "'a set \<Rightarrow> 'r1 \<Rightarrow> 'r2" (infixr "\<lhd>" 65)

adhoc_overloading 
  dom_res rel_domres
  and dom_res pdom_res
  and dom_res fdom_res

subsection \<open> Range restriction \<close>

consts ran_res :: "'a set \<Rightarrow> 'r1 \<Rightarrow> 'r2" (infixr "\<rhd>" 65)

adhoc_overloading 
(*  ran_res rel_ranres *)
  ran_res pran_res
  and dom_res fran_res

subsection \<open> Domain subtraction \<close>

subsection \<open> Range subtraction \<close>

subsection \<open> Relational inversion \<close>

notation converse ("(_\<^sup>\<sim>)" [1000] 999)

lemma relational_inverse: "r\<^sup>\<sim> = {(p.2, p.1) | p. p \<in> r}"
  by auto
  
end
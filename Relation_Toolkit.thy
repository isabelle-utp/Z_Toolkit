section \<open> Relations \<close>

theory Relation_Toolkit
  imports Set_Toolkit Relation_Extra Partial_Fun Finite_Fun Total_Fun
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
  probably we want to compose two functions, rather than two relations. This makes sense,
  given that relational composition and functional composition are semantically identical 
  (but reversed). \<close>

no_notation comp (infixl "\<circ>" 55)
notation pfun_comp (infixl "\<circ>" 55)

(*
consts fcomp :: "'r1 \<Rightarrow> 'r2 \<Rightarrow> 'r3" (infixl "\<circ>" 55)

text \<open> Since adhoc overloading and subtype coercion are mutually exclusive, we need to explicitly
  create all the variants for composing relations and different subclasses. This has the benefit
  that the most specific implementation is picked. \<close>

abbreviation (input) "rel_rel_fcomp P Q \<equiv> Q O P"
abbreviation (input) "pfun_rel_fcomp P Q \<equiv> Q O pfun_graph P"
abbreviation (input) "rel_pfun_fcomp P Q \<equiv> pfun_graph Q O P"
abbreviation (input) "ffun_pfun_fcomp P Q \<equiv> Q \<circ>\<^sub>p pfun_of P"
abbreviation (input) "pfun_ffun_fcomp P Q \<equiv> pfun_of Q \<circ>\<^sub>p P"
abbreviation (input) "ffun_rel_fcomp P Q \<equiv> Q O ffun_graph P"
abbreviation (input) "rel_ffun_fcomp P Q \<equiv> ffun_graph Q O P"

adhoc_overloading fcomp comp 
  and fcomp rel_rel_fcomp
  and fcomp pfun_rel_fcomp
  and fcomp rel_pfun_fcomp
  and fcomp pfun_comp
  and fcomp ffun_pfun_fcomp
  and fcomp pfun_ffun_fcomp
  and fcomp ffun_rel_fcomp
  and fcomp rel_ffun_fcomp
  and fcomp ffun_comp
*)

subsection \<open> Domain restriction \<close>

consts dom_res :: "'a set \<Rightarrow> 'r1 \<Rightarrow> 'r2" (infixr "\<lhd>" 65)

adhoc_overloading 
  dom_res rel_domres
  and dom_res pdom_res
  and dom_res fdom_res

subsection \<open> Range restriction \<close>

subsection \<open> Domain subtraction \<close>

subsection \<open> Range subtraction \<close>

subsection \<open> Relational inversion \<close>

notation converse ("(_\<^sup>\<sim>)" [1000] 999)

lemma relational_inverse: "r\<^sup>\<sim> = {(p.2, p.1) | p. p \<in> r}"
  by auto
  
end
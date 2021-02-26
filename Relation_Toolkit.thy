section \<open> Relation Toolkit \<close>

theory Relation_Toolkit
  imports Set_Toolkit Overriding
begin

subsection \<open> Conversions \<close>

text \<open> The majority of the relation toolkit is also part of HOL. We just need to generalise
  some of the syntax. \<close>

declare [[coercion rel_apply]]
declare [[coercion pfun_app]]
declare [[coercion pfun_of]]
declare [[coercion pfun_graph]]
(* declare [[coercion ffun_graph]] *)

notation pfun_graph ("\<lbrakk>_\<rbrakk>\<^sub>p")
notation ffun_graph ("\<lbrakk>_\<rbrakk>\<^sub>f")

subsection \<open> First component projection \<close>

text \<open> Z supports n-ary Cartesian products. We cannot support such structures directly in 
  Isabelle/HOL, but instead add the projection notations for the first and second components.
  A homogeneous finite Cartesian product type also exists in the Multivariate Analysis package. \<close>

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

subsection \<open> Domain restriction and subtraction \<close>

consts dom_res :: "'a set \<Rightarrow> 'r \<Rightarrow> 'r" (infixr "\<lhd>" 65)

abbreviation ndres (infixr "-\<lhd>" 65) where "ndres A P \<equiv> CONST dom_res (- A) P" 

adhoc_overloading 
  dom_res rel_domres
  and dom_res pdom_res
  and dom_res fdom_res

syntax "_ndres" :: "logic \<Rightarrow> logic \<Rightarrow> logic" 
translations "_ndres A P" == "CONST dom_res (- A) P"

subsection \<open> Range restriction and subtraction \<close>

consts ran_res :: "'r \<Rightarrow> 'a set \<Rightarrow> 'r" (infixl "\<rhd>" 65)

abbreviation nrres (infixl "\<rhd>-" 65) where "nrres P A \<equiv> CONST ran_res P (- A)"

adhoc_overloading 
  ran_res rel_ranres
  and ran_res pran_res
  and dom_res fran_res

subsection \<open> Relational inversion \<close>

notation converse ("(_\<^sup>\<sim>)" [1000] 999)

lemma relational_inverse: "r\<^sup>\<sim> = {(p.2, p.1) | p. p \<in> r}"
  by auto

subsection \<open> Relational image \<close>

notation Image ("_\<lparr>_\<rparr>" [990] 990)

lemma Image_eq: "r\<lparr>a\<rparr> = {p.2 | p. p \<in> r \<and> p.1 \<in> a}"
  by (auto simp add: Image_def)

subsection \<open> Overriding \<close>

lemma override_eq: "r \<oplus> s = ((- dom s) \<lhd> r) \<union> s"
  by (simp add: oplus_set_def rel_override_def)

lemma dom_override: "dom (Q \<oplus> R) = (dom Q) \<union> (dom R)"
  by (simp add: override_eq Domain_Un_eq Un_Int_distrib2)

lemma override_Un: "dom Q \<inter> dom R = {} \<Longrightarrow> Q \<oplus> R = Q \<union> R"
  by (simp add: override_eq Int_commute rel_domres_compl_disj)

end
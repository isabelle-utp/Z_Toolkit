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

consts dom :: "'f \<Rightarrow> 'a set"

adhoc_overloading
  dom Map.dom and
  dom Relation.Domain and
  dom Partial_Fun.pdom and
  dom Finite_Fun.fdom

subsection \<open> Range \<close>

hide_const (open) ran

consts ran :: "'f \<Rightarrow> 'a set"

adhoc_overloading
  ran Map.ran and
  ran Relation.Range and
  ran Partial_Fun.pran and
  ran Finite_Fun.fran

subsection \<open> Identity relation \<close>

notation Id_on ("id[_]")

subsection \<open> Relational composition \<close>

notation relcomp (infixr "\<^bold>;" 75)

subsection \<open> Functional composition \<close>

text \<open> Composition is probably the most difficult of the Z functions to implement correctly. Firstly,
  the notation @{term "(\<circ>)"} is already defined for HOL functions, and we need to respect that
  in order to use the HOL library functions. Secondly, Z composition can be used to compose 
  heterogeneous relations and functions, which is not easy to type infer. Consequently, we opt
  to use adhoc overloading here. \<close>

hide_const (open) comp

consts comp :: "'f \<Rightarrow> 'g \<Rightarrow> 'h" 

adhoc_overloading
  comp Fun.comp and
  comp pfun_comp and
  comp ffun_comp

bundle Z_Relation_Syntax
begin

no_notation Fun.comp (infixl "\<circ>" 55)
notation comp (infixl "\<circ>" 55)

end

subsection \<open> Domain restriction and subtraction \<close>

consts dom_res :: "'a set \<Rightarrow> 'r \<Rightarrow> 'r" (infixr "\<Zdres>" 85)

abbreviation ndres (infixr "\<Zndres>" 85) where "ndres A P \<equiv> CONST dom_res (- A) P" 

adhoc_overloading 
  dom_res rel_domres
  and dom_res pdom_res
  and dom_res fdom_res

syntax "_ndres" :: "logic \<Rightarrow> logic \<Rightarrow> logic" 
translations "_ndres A P" == "CONST dom_res (- A) P"

subsection \<open> Range restriction and subtraction \<close>

consts ran_res :: "'r \<Rightarrow> 'a set \<Rightarrow> 'r" (infixl "\<Zrres>" 86)

abbreviation nrres (infixl "\<Znrres>" 86) where "nrres P A \<equiv> CONST ran_res P (- A)"

adhoc_overloading 
  ran_res rel_ranres
  and ran_res pran_res
  and dom_res fran_res

subsection \<open> Relational inversion \<close>

notation converse ("(_\<^sup>\<sim>)" [1000] 999)

lemma relational_inverse: "r\<^sup>\<sim> = {(p.2, p.1) | p. p \<in> r}"
  by auto

subsection \<open> Relational image \<close>

hide_const (open) Set.image

consts image :: "'f \<Rightarrow> 'a set \<Rightarrow> 'b set"

notation image ("_\<lparr>_\<rparr>" [990] 990)

adhoc_overloading
  image Set.image and
  image Relation.Image

lemma Image_eq: "Image r a = {p.2 | p. p \<in> r \<and> p.1 \<in> a}"
  by (auto simp add: Image_def)

subsection \<open> Overriding \<close>

lemma override_eq: "r \<oplus> s = ((- dom s) \<Zdres> r) \<union> s"
  by (simp add: oplus_set_def)

lemma dom_override: "dom ((Q :: 'a \<leftrightarrow> 'b) \<oplus> R) = (dom Q) \<union> (dom R)"
  by (simp add: override_eq Domain_Un_eq Un_Int_distrib2)

lemma override_Un: "dom Q \<inter> dom R = {} \<Longrightarrow> Q \<oplus> R = Q \<union> R"
  by (simp add: override_eq Int_commute rel_domres_compl_disj)

end
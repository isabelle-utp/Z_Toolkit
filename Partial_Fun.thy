(******************************************************************************)
(* Project: Isabelle/UTP Toolkit                                              *)
(* File: Partial_Fun.thy                                                      *)
(* Authors: Simon Foster and Frank Zeyda                                      *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

section \<open> Partial Functions \<close>

theory Partial_Fun
imports "Optics.Lenses" Map_Extra "HOL-Library.Mapping"
begin

text \<open> I'm not completely satisfied with partial functions as provided by Map.thy, since they don't
        have a unique type and so we can't instantiate classes, make use of adhoc-overloading
        etc. Consequently I've created a new type and derived the laws. \<close>

subsection \<open> Partial function type and operations \<close>

typedef ('a, 'b) pfun = "UNIV :: ('a \<rightharpoonup> 'b) set"
  morphisms pfun_lookup pfun_of_map ..

type_notation pfun (infixr "\<Rightarrow>\<^sub>p" 0)

setup_lifting type_definition_pfun

lemma pfun_lookup_map [simp]: "pfun_lookup (pfun_of_map f) = f"
  by (simp add: pfun_of_map_inverse)

lift_bnf ('k, pran: 'v) pfun [wits: "Map.empty :: 'k \<Rightarrow> 'v option"] for map: map_pfun rel: relt_pfun
  by auto

declare pfun.map_transfer [transfer_rule]

instantiation pfun :: (type, type) equal
begin

definition "HOL.equal m1 m2 \<longleftrightarrow> (\<forall>k. pfun_lookup m1 k = pfun_lookup m2 k)"

instance 
  by (intro_classes, auto simp add: equal_pfun_def, transfer, auto)

end

lift_definition pfun_app :: "('a, 'b) pfun \<Rightarrow> 'a \<Rightarrow> 'b" ("_'(_')\<^sub>p" [999,0] 999) is 
"\<lambda> f x. if (x \<in> dom f) then the (f x) else undefined" .

lift_definition pfun_upd :: "('a, 'b) pfun \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pfun"
is "\<lambda> f k v. f(k := Some v)" .

lift_definition pdom :: "('a, 'b) pfun \<Rightarrow> 'a set" is dom .

lemma pran_rep_eq [transfer_rule]: "pran f = ran (pfun_lookup f)"
  by (transfer, auto simp add: ran_def)

lift_definition pfun_comp :: "('b, 'c) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> ('a, 'c) pfun" (infixl "\<circ>\<^sub>p" 55) is map_comp .

lift_definition map_pfun' :: "('c \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> ('a, 'b) pfun \<Rightarrow> ('c, 'd) pfun"
  is "\<lambda>f g m. (map_option g \<circ> m \<circ> f)" parametric map_parametric .

functor map_pfun'
  by (transfer, auto simp add: fun_eq_iff option.map_comp option.map_id)+

lift_definition pfun_member :: "'a \<times> 'b \<Rightarrow> ('a, 'b) pfun \<Rightarrow> bool" (infix "\<in>\<^sub>p" 50) is "(\<in>\<^sub>m)" .

lift_definition pfun_inj :: "('a, 'b) pfun \<Rightarrow> bool" is "\<lambda> f. inj_on f (dom f)" .

lift_definition pfun_inv :: "('a, 'b) pfun \<Rightarrow> ('b, 'a) pfun" is map_inv .

lift_definition pId_on :: "'a set \<Rightarrow> ('a, 'a) pfun" is "\<lambda> A x. if (x \<in> A) then Some x else None" .

abbreviation pId :: "('a, 'a) pfun" where
"pId \<equiv> pId_on UNIV"

lift_definition pdom_res :: "'a set \<Rightarrow> ('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun" (infixr "\<lhd>\<^sub>p" 85)
is "\<lambda> A f. restrict_map f A" .

lift_definition pran_res :: "('a, 'b) pfun \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) pfun" (infixl "\<rhd>\<^sub>p" 86)
is ran_restrict_map .

lift_definition pfun_graph :: "('a, 'b) pfun \<Rightarrow> ('a \<times> 'b) set" is map_graph .

lift_definition graph_pfun :: "('a \<times> 'b) set \<Rightarrow> ('a, 'b) pfun" is graph_map .

lift_definition pfun_entries :: "'k set \<Rightarrow> ('k \<Rightarrow> 'v) \<Rightarrow> ('k, 'v) pfun" is
"\<lambda> d f x. if (x \<in> d) then Some (f x) else None" .

definition pfuse :: "('a \<Rightarrow>\<^sub>p 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>p 'c) \<Rightarrow> ('a \<Rightarrow>\<^sub>p 'b \<times> 'c)"
  where "pfuse f g = pfun_entries (pdom(f) \<inter> pdom(g)) (\<lambda> x. (pfun_app f x, pfun_app g x))"

lift_definition ptabulate :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) pfun"
  is "\<lambda>ks f. (map_of (List.map (\<lambda>k. (k, f k)) ks))" .

lift_definition pcombine ::
  "('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun"
  is "\<lambda>f m1 m2 x. combine_options f (m1 x) (m2 x)" .

abbreviation "fun_pfun \<equiv> pfun_entries UNIV"

no_notation disj (infixr "|" 30)

definition pabs :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow>\<^sub>p 'b" where
"pabs A P f = (A \<inter> Collect P) \<lhd>\<^sub>p fun_pfun f"

definition pcard :: "('a, 'b) pfun \<Rightarrow> nat"
where "pcard f = card (pdom f)"

instantiation pfun :: (type, type) zero
begin
lift_definition zero_pfun :: "('a, 'b) pfun" is "Map.empty" .
instance ..
end

abbreviation pempty :: "('a, 'b) pfun" ("{}\<^sub>p")
where "pempty \<equiv> 0"

instantiation pfun :: (type, type) plus
begin
lift_definition plus_pfun :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun" is "(++)" .
instance ..
end

instantiation pfun :: (type, type) minus
begin
lift_definition minus_pfun :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun" is "(--)" .
instance ..
end

instance pfun :: (type, type) monoid_add
  by (intro_classes, (transfer, auto)+)

instantiation pfun :: (type, type) inf
begin
lift_definition inf_pfun :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun" is
"\<lambda> f g x. if (x \<in> dom(f) \<inter> dom(g) \<and> f(x) = g(x)) then f(x) else None" .
instance ..
end

abbreviation pfun_inter :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun" (infixl "\<inter>\<^sub>p" 80)
where "pfun_inter \<equiv> inf"

instantiation pfun :: (type, type) order
begin
  lift_definition less_eq_pfun :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> bool" is
  "\<lambda> f g. f \<subseteq>\<^sub>m g" .
  lift_definition less_pfun :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> bool" is
  "\<lambda> f g. f \<subseteq>\<^sub>m g \<and> f \<noteq> g" .
instance
  by (intro_classes, (transfer, auto intro: map_le_trans simp add: map_le_antisym)+)
end

abbreviation pfun_subset :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> bool" (infix "\<subset>\<^sub>p" 50)
where "pfun_subset \<equiv> less"

abbreviation pfun_subset_eq :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> bool" (infix "\<subseteq>\<^sub>p" 50)
where "pfun_subset_eq \<equiv> less_eq"

instance pfun :: (type, type) semilattice_inf
  by (intro_classes, (transfer, auto simp add: map_le_def dom_def)+)

lemma pfun_subset_eq_least [simp]:
  "{}\<^sub>p \<subseteq>\<^sub>p f"
  by (transfer, auto)

syntax
  "_PfunUpd"  :: "[('a, 'b) pfun, maplets] => ('a, 'b) pfun" ("_'(_')\<^sub>p" [900,0]900)
  "_Pfun"     :: "maplets => ('a, 'b) pfun"            ("(1{_}\<^sub>p)")
  "_pabs"      :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<lambda> _ \<in> _ | _ \<bullet> _" [0, 0, 0, 10] 10)
  "_pabs_mem"  :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<lambda> _ \<in> _ \<bullet> _" [0, 0, 10] 10)
  "_pabs_pred" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<lambda> _ | _ \<bullet> _" [0, 0, 10] 10)
  "_pabs_tot"  :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<lambda> _ \<bullet> _" [0, 10] 10)

translations
  "_PfunUpd m (_Maplets xy ms)"  == "_PfunUpd (_PfunUpd m xy) ms"
  "_PfunUpd m (_maplet  x y)"    == "CONST pfun_upd m x y"
  "_Pfun ms"                     => "_PfunUpd (CONST pempty) ms"
  "_Pfun (_Maplets ms1 ms2)"     <= "_PfunUpd (_Pfun ms1) ms2"
  "_Pfun ms"                     <= "_PfunUpd (CONST pempty) ms"
  "_pabs x A P f" => "CONST pabs A (\<lambda> x. P) (\<lambda> x. f)"
  "_pabs x A P f" <= "CONST pabs A (\<lambda> y. P) (\<lambda> x. f)"
  "_pabs x A P (f x)" <= "CONST pabs A (\<lambda> x. P) f"
  "_pabs_mem x A f" == "_pabs x A (CONST True) f"
  "_pabs_pred x P f" == "_pabs x (CONST UNIV) P f"
  "_pabs_tot x f" == "_pabs_pred x (CONST True) f"
  "_pabs_tot x f" <= "_pabs_mem x (CONST UNIV) f"

subsection \<open> Algebraic laws \<close>

lemma pfun_comp_assoc: "f \<circ>\<^sub>p (g \<circ>\<^sub>p h) = (f \<circ>\<^sub>p g) \<circ>\<^sub>p h"
  by (transfer, simp add: map_comp_assoc)

lemma pfun_comp_left_id [simp]: "pId \<circ>\<^sub>p f = f"
  by (transfer, auto)

lemma pfun_comp_right_id [simp]: "f \<circ>\<^sub>p pId = f"
  by (transfer, auto)

lemma pfun_comp_left_zero [simp]: "{}\<^sub>p \<circ>\<^sub>p f = {}\<^sub>p"
  by (transfer, auto)

lemma pfun_comp_right_zero [simp]: "f \<circ>\<^sub>p {}\<^sub>p = {}\<^sub>p"
  by (transfer, auto)

lemma pfun_override_dist_comp:
  "(f + g) \<circ>\<^sub>p h = (f \<circ>\<^sub>p h) + (g \<circ>\<^sub>p h)"
  apply (transfer)
  apply (rule ext)
  apply (auto simp add: map_add_def)
  apply (rename_tac f g h x)
  apply (case_tac "h x")
   apply (auto)
  apply (rename_tac f g h x y)
  apply (case_tac "g y")
   apply (auto)
  done

lemma pfun_minus_unit [simp]:
  fixes f :: "('a, 'b) pfun"
  shows "f - 0 = f"
  by (transfer, simp add: map_minus_def)

lemma pfun_minus_zero [simp]:
  fixes f :: "('a, 'b) pfun"
  shows "0 - f = 0"
  by (transfer, simp add: map_minus_def)

lemma pfun_minus_self [simp]:
  fixes f :: "('a, 'b) pfun"
  shows "f - f = 0"
  by (transfer, simp add: map_minus_def)

lemma pfun_plus_idem [simp]: "(f :: 'a \<Rightarrow>\<^sub>p 'b) + f = f"
  by (transfer, simp add: map_add_subsumed2)

lemma pfun_plus_commute:
  "pdom(f) \<inter> pdom(g) = {} \<Longrightarrow> f + g = g + f"
  by (transfer, metis map_add_comm)

lemma pfun_plus_commute_weak:
  "(\<forall> k \<in> pdom(f) \<inter> pdom(g). f(k)\<^sub>p = g(k)\<^sub>p) \<Longrightarrow> f + g = g + f"
  by (transfer, simp, metis IntD1 IntD2 domD map_add_comm_weak option.sel)

lemma pfun_minus_plus_commute:
  "pdom(g) \<inter> pdom(h) = {} \<Longrightarrow> (f - g) + h = (f + h) - g"
  by (transfer, simp add: map_minus_plus_commute)

lemma pfun_plus_minus:
  "f \<subseteq>\<^sub>p g \<Longrightarrow> (g - f) + f = g"
  by (transfer, rule ext, auto simp add: map_le_def map_minus_def map_add_def option.case_eq_if)

lemma pfun_minus_common_subset:
  "\<lbrakk> h \<subseteq>\<^sub>p f; h \<subseteq>\<^sub>p g \<rbrakk> \<Longrightarrow> (f - h = g - h) = (f = g)"
  by (transfer, simp add: map_minus_common_subset)

lemma pfun_minus_plus:
  "pdom(f) \<inter> pdom(g) = {} \<Longrightarrow> (f + g) - g = f"
  by (transfer, simp add: map_add_def map_minus_def option.case_eq_if, rule ext, auto)
     (metis Int_commute domIff insert_disjoint(1) insert_dom)

lemma pfun_plus_pos: "x + y = {}\<^sub>p \<Longrightarrow> x = {}\<^sub>p"
  by (transfer, simp)

lemma pfun_le_plus: "pdom x \<inter> pdom y = {} \<Longrightarrow> x \<le> x + y"
  by (transfer, auto simp add: map_le_iff_add)

subsection \<open> Membership, application, and update \<close>

lemma pfun_ext: "\<lbrakk> \<And> x y. (x, y) \<in>\<^sub>p f \<longleftrightarrow> (x, y) \<in>\<^sub>p g \<rbrakk> \<Longrightarrow> f = g"
  by (transfer, simp add: map_ext)

lemma pfun_member_alt_def:
  "(x, y) \<in>\<^sub>p f \<longleftrightarrow> (x \<in> pdom f \<and> f(x)\<^sub>p = y)"
  by (transfer, auto simp add: map_member_alt_def map_apply_def)

lemma pfun_member_plus:
  "(x, y) \<in>\<^sub>p f + g \<longleftrightarrow> ((x \<notin> pdom(g) \<and> (x, y) \<in>\<^sub>p f) \<or> (x, y) \<in>\<^sub>p g)"
  by (transfer, simp add: map_member_plus)

lemma pfun_member_minus:
  "(x, y) \<in>\<^sub>p f - g \<longleftrightarrow> (x, y) \<in>\<^sub>p f \<and> (\<not> (x, y) \<in>\<^sub>p g)"
  by (transfer, simp add: map_member_minus)

lemma pfun_app_map [simp]: "(pfun_of_map f)(x)\<^sub>p = (if (x \<in> dom(f)) then the (f x) else undefined)"
  by (transfer, simp)

lemma pfun_app_upd_1 [simp]: "x = y \<Longrightarrow> (f(x \<mapsto> v)\<^sub>p)(y)\<^sub>p = v"
  by (transfer, simp)

lemma pfun_app_upd_2 [simp]: "x \<noteq> y \<Longrightarrow> (f(x \<mapsto> v)\<^sub>p)(y)\<^sub>p = f(y)\<^sub>p"
  by (transfer, simp)

lemma pfun_graph_apply [simp]: "rel_apply (pfun_graph f) x = f(x)\<^sub>p"
  by (transfer, auto simp add: rel_apply_def map_graph_def)

lemma pfun_upd_ext [simp]: "x \<in> pdom(f) \<Longrightarrow> f(x \<mapsto> f(x)\<^sub>p)\<^sub>p = f"
  by (transfer, simp add: domIff)

lemma pfun_app_add [simp]: "x \<in> pdom(g) \<Longrightarrow> (f + g)(x)\<^sub>p = g(x)\<^sub>p"
  by (transfer, auto)

lemma pfun_upd_add [simp]: "f + g(x \<mapsto> v)\<^sub>p = (f + g)(x \<mapsto> v)\<^sub>p"
  by (transfer, simp)

lemma pfun_upd_add_left [simp]: "x \<notin> pdom(g) \<Longrightarrow> f(x \<mapsto> v)\<^sub>p + g = (f + g)(x \<mapsto> v)\<^sub>p"
  by (transfer, auto, metis domD map_add_upd_left)

lemma pfun_app_add' [simp]: "\<lbrakk> e \<in> pdom f; e \<notin> pdom g \<rbrakk> \<Longrightarrow> (f + g)(e)\<^sub>p = f(e)\<^sub>p"
  by (metis (no_types, lifting) pfun_app_upd_1 pfun_upd_add_left pfun_upd_ext)

lemma pfun_upd_twice [simp]: "f(x \<mapsto> u, x \<mapsto> v)\<^sub>p = f(x \<mapsto> v)\<^sub>p"
  by (transfer, simp)

lemma pfun_upd_comm:
  assumes "x \<noteq> y"
  shows "f(y \<mapsto> u, x \<mapsto> v)\<^sub>p = f(x \<mapsto> v, y \<mapsto> u)\<^sub>p"
  using assms by (transfer, auto)

lemma pfun_upd_comm_linorder [simp]:
  fixes x y :: "'a :: linorder"
  assumes "x < y"
  shows "f(y \<mapsto> u, x \<mapsto> v)\<^sub>p = f(x \<mapsto> v, y \<mapsto> u)\<^sub>p"
  using assms by (transfer, auto)

lemma pfun_upd_as_ovrd: "f(k \<mapsto> v)\<^sub>p = f + {k \<mapsto> v}\<^sub>p"
  by (transfer, simp)

lemma pfun_ovrd_single_upd: "x \<in> pdom(g) \<Longrightarrow> f + ({x} \<lhd>\<^sub>p g) = f(x \<mapsto> g(x)\<^sub>p)\<^sub>p"
  by (transfer, auto simp add: map_add_def restrict_map_def fun_eq_iff)

lemma pfun_app_minus [simp]: "x \<notin> pdom g \<Longrightarrow> (f - g)(x)\<^sub>p = f(x)\<^sub>p"
  by (transfer, auto simp add: map_minus_def)

lemma pfun_app_empty [simp]: "{}\<^sub>p(x)\<^sub>p = undefined"
  by (transfer, simp)

lemma pfun_app_not_in_dom: 
  "x \<notin> pdom(f) \<Longrightarrow> f(x)\<^sub>p = undefined"
  by (transfer, simp)

lemma pfun_upd_minus [simp]:
  "x \<notin> pdom g \<Longrightarrow> (f - g)(x \<mapsto> v)\<^sub>p = (f(x \<mapsto> v)\<^sub>p - g)"
  by (transfer, auto simp add: map_minus_def)

lemma pdom_member_minus_iff [simp]:
  "x \<notin> pdom g \<Longrightarrow> x \<in> pdom(f - g) \<longleftrightarrow> x \<in> pdom(f)"
  by (transfer, simp add: domIff map_minus_def)

lemma psubseteq_pfun_upd1 [intro]:
  "\<lbrakk> f \<subseteq>\<^sub>p g; x \<notin> pdom(g) \<rbrakk> \<Longrightarrow> f \<subseteq>\<^sub>p g(x \<mapsto> v)\<^sub>p"
  by (transfer, auto simp add: map_le_def dom_def)

lemma psubseteq_pfun_upd2 [intro]:
  "\<lbrakk> f \<subseteq>\<^sub>p g; x \<notin> pdom(f) \<rbrakk> \<Longrightarrow> f \<subseteq>\<^sub>p g(x \<mapsto> v)\<^sub>p"
  by (transfer, auto simp add: map_le_def dom_def)

lemma psubseteq_pfun_upd3 [intro]:
  "\<lbrakk> f \<subseteq>\<^sub>p g; g(x)\<^sub>p = v \<rbrakk> \<Longrightarrow> f \<subseteq>\<^sub>p g(x \<mapsto> v)\<^sub>p"
  by (transfer, auto simp add: map_le_def dom_def)

lemma psubseteq_dom_subset:
  "f \<subseteq>\<^sub>p g \<Longrightarrow> pdom(f) \<subseteq> pdom(g)"
  by (transfer, auto simp add: map_le_def dom_def)

lemma psubseteq_ran_subset:
  "f \<subseteq>\<^sub>p g \<Longrightarrow> pran(f) \<subseteq> pran(g)"
  by (transfer, auto simp add: map_le_def dom_def ran_def)

lemma pfun_eq_iff: "f = g \<longleftrightarrow> (pdom(f) = pdom(g) \<and> (\<forall> x \<in> pdom(f). f(x)\<^sub>p = g(x)\<^sub>p))"
  by (auto, transfer, simp add: map_eq_iff, metis domD option.sel)

subsection \<open> Map laws \<close>

lemma map_pfun_empty [simp]: "map_pfun f {}\<^sub>p = {}\<^sub>p"
  by (transfer, simp)

lemma map_pfun'_empty [simp]: "map_pfun' f g {}\<^sub>p = {}\<^sub>p"
  unfolding map_pfun'_def by (transfer, simp add: comp_def)

lemma map_pfun_upd [simp]: "map_pfun f (g(x \<mapsto> v)\<^sub>p) = (map_pfun f g)(x \<mapsto> f v)\<^sub>p"
  by (simp add: map_pfun_def pfun_upd.rep_eq pfun_upd.abs_eq)

lemma map_pfun_apply [simp]: "x \<in> pdom G \<Longrightarrow> (map_pfun F G)(x)\<^sub>p = F(G(x)\<^sub>p)"
  unfolding map_pfun_def by (auto simp add: pfun_app.rep_eq domD pdom.rep_eq)

lemma map_pfun_as_pabs: "map_pfun f g = (\<lambda> x \<in> pdom(g) \<bullet> f(g(x)\<^sub>p))"
  by (simp add: pabs_def, transfer, auto simp add: fun_eq_iff restrict_map_def)

lemma map_pfun_ovrd [simp]: "map_pfun f (g + h) = (map_pfun f g) + (map_pfun f h)"
  by (simp add: map_pfun_def, transfer, auto simp add: map_add_def fun_eq_iff)
     (metis bind.bind_lunit comp_apply map_conv_bind_option option.case_eq_if)

lemma map_pfun_dres [simp]: "map_pfun f (A \<lhd>\<^sub>p g) = A \<lhd>\<^sub>p map_pfun f g"
  by (simp add: map_pfun_def, transfer, auto simp add: restrict_map_def)

subsection \<open> Domain laws \<close>

lemma pdom_zero [simp]: "pdom 0 = {}"
  by (transfer, simp)

lemma pdom_pId_on [simp]: "pdom (pId_on A) = A"
  by (transfer, auto)

lemma pdom_plus [simp]: "pdom (f + g) = pdom f \<union> pdom g"
  by (transfer, auto)

lemma pdom_minus [simp]: "g \<le> f \<Longrightarrow> pdom (f - g) = pdom f - pdom g"
  apply (transfer, auto simp add: map_minus_def)
  apply (meson option.distinct(1))
  apply (metis domIff map_le_def option.simps(3))
  done

lemma pdom_inter: "pdom (f \<inter>\<^sub>p g) \<subseteq> pdom f \<inter> pdom g"
  by (transfer, auto simp add: dom_def)

lemma pdom_comp [simp]: "pdom (g \<circ>\<^sub>p f) = pdom (f \<rhd>\<^sub>p pdom g)"
  by (transfer, auto simp add: ran_restrict_map_def)

lemma pdom_upd [simp]: "pdom (f(k \<mapsto> v)\<^sub>p) = insert k (pdom f)"
  by (transfer, simp)

lemma pdom_pdom_res [simp]: "pdom (A \<lhd>\<^sub>p f) = A \<inter> pdom(f)"
  by (transfer, auto)

lemma pdom_graph_pfun [simp]: "pdom (graph_pfun R) = Domain R"
  by (transfer, simp add: Domain_fst graph_map_dom)

lemma pdom_pran_res_finite [simp]:
  "finite (pdom f) \<Longrightarrow> finite (pdom (f \<rhd>\<^sub>p A))"
  by (transfer, auto)

lemma pdom_pfun_graph_finite [simp]:
  "finite (pdom f) \<Longrightarrow> finite (pfun_graph f)"
  by (transfer, simp add: finite_dom_graph)

lemma pdom_map_pfun [simp]: "pdom (map_pfun F G) = pdom G"
  unfolding map_pfun_def by (auto; metis dom_map_option_comp pdom.abs_eq pdom.rep_eq)

subsection \<open> Range laws \<close>

lemma pran_zero [simp]: "pran 0 = {}"
  by (transfer, simp)

lemma pran_pId_on [simp]: "pran (pId_on A) = A"
  by (transfer, auto simp add: ran_def)

lemma pran_upd [simp]: "pran (f(k \<mapsto> v)\<^sub>p) = insert v (pran ((- {k}) \<lhd>\<^sub>p f))"
  by (transfer, auto simp add: ran_def restrict_map_def)

lemma pran_pran_res [simp]: "pran (f \<rhd>\<^sub>p A) = pran(f) \<inter> A"
  by (transfer, auto simp add: ran_restrict_map_def)

lemma pran_comp [simp]: "pran (g \<circ>\<^sub>p f) = pran (pran f \<lhd>\<^sub>p g)"
  by (transfer, auto simp add: ran_def restrict_map_def)

lemma pran_finite [simp]: "finite (pdom f) \<Longrightarrow> finite (pran f)"
  by (simp add: pdom.rep_eq pran_rep_eq)

lemma pran_pdom: "pran F = pfun_app F ` pdom F"
  by (transfer, force simp add: dom_def)

subsection \<open> Partial Injections \<close>

lemma pfun_inj_empty [simp]: "pfun_inj {}\<^sub>p"
  by (transfer, simp)

lemma pinj_pId_on [simp]: "pfun_inj (pId_on A)"
  by (transfer, auto simp add: inj_on_def)

lemma pfun_inj_inv_inv: "pfun_inj f \<Longrightarrow> pfun_inv (pfun_inv f) = f"
  by (transfer, simp)

lemma pfun_inj_inv: "pfun_inj f \<Longrightarrow> pfun_inj (pfun_inv f)"
  by (transfer, simp add: inj_map_inv)

lemma pfun_inj_upd: "\<lbrakk> pfun_inj f; v \<notin> pran f \<rbrakk> \<Longrightarrow> pfun_inj (f(k \<mapsto> v)\<^sub>p)"
  by (transfer, auto, meson f_the_inv_into_f inj_on_fun_updI)

lemma pfun_inj_dres: "pfun_inj f \<Longrightarrow> pfun_inj (A \<lhd>\<^sub>p f)"
  by (transfer, auto simp add: inj_on_def)

lemma pfun_inj_rres: "pfun_inj f \<Longrightarrow> pfun_inj (f \<rhd>\<^sub>p A)"
  by (transfer, auto simp add: inj_on_def ran_restrict_map_def, metis domI option.simps(3))

lemma pfun_inj_comp: "\<lbrakk> pfun_inj f; pfun_inj g \<rbrakk> \<Longrightarrow> pfun_inj (f \<circ>\<^sub>p g)"
  by (transfer, auto simp add: inj_on_def map_comp_def option.case_eq_if dom_def)

lemma pfun_inv_dres: "pfun_inj f \<Longrightarrow> pfun_inv (A \<lhd>\<^sub>p f) = (pfun_inv f) \<rhd>\<^sub>p A"
  by (transfer, simp add: map_inv_dom_res)

lemma pfun_inv_rres: "pfun_inj f \<Longrightarrow> pfun_inv (f \<rhd>\<^sub>p A) = A \<lhd>\<^sub>p (pfun_inv f)"
  by (transfer, simp add: map_inv_ran_res)

lemma pfun_inv_empty [simp]: "pfun_inv {}\<^sub>p = {}\<^sub>p"
  by (transfer, simp)

lemma pdom_pfun_inv [simp]: "pdom (pfun_inv f) = pran f"
  by (simp add: pran_rep_eq, transfer, simp)

lemma pfun_inv_add:
  assumes "pfun_inj f" "pfun_inj g" "pran f \<inter> pran g = {}"
  shows "pfun_inv (f + g) = (pfun_inv f \<rhd>\<^sub>p (- pdom g)) + pfun_inv g"
  using assms by (simp add: pran_rep_eq, transfer, auto, meson map_inv_add)

lemma pfun_inv_upd:
  assumes "pfun_inj f" "v \<notin> pran f"
  shows "pfun_inv (f(k \<mapsto> v)\<^sub>p) = (pfun_inv ((- {k}) \<lhd>\<^sub>p f))(v \<mapsto> k)\<^sub>p"
  using assms by (simp add: pran_rep_eq, transfer, meson map_inv_upd)

subsection \<open> Domain restriction laws \<close>

lemma pdom_res_zero [simp]: "A \<lhd>\<^sub>p {}\<^sub>p = {}\<^sub>p"
  by (transfer, auto)

lemma pdom_res_empty [simp]:
  "({} \<lhd>\<^sub>p f) = {}\<^sub>p"
  by (transfer, auto)

lemma pdom_res_pdom [simp]:
  "pdom(f) \<lhd>\<^sub>p f = f"
  by (transfer, auto)

lemma pdom_res_UNIV [simp]: "UNIV \<lhd>\<^sub>p f = f"
  by (transfer, auto)
    
lemma pdom_res_alt_def: "A \<lhd>\<^sub>p f =  f \<circ>\<^sub>p pId_on A"
  by (transfer, rule ext, auto simp add: restrict_map_def)

lemma pdom_res_upd_in [simp]:
  "k \<in> A \<Longrightarrow> A \<lhd>\<^sub>p f(k \<mapsto> v)\<^sub>p = (A \<lhd>\<^sub>p f)(k \<mapsto> v)\<^sub>p"
  by (transfer, auto)

lemma pdom_res_upd_out [simp]:
  "k \<notin> A \<Longrightarrow> A \<lhd>\<^sub>p f(k \<mapsto> v)\<^sub>p = A \<lhd>\<^sub>p f"
  by (transfer, auto)
    
lemma pfun_pdom_antires_upd [simp]:
  "k \<in> A \<Longrightarrow> ((- A) \<lhd>\<^sub>p m)(k \<mapsto> v)\<^sub>p =  ((- (A - {k})) \<lhd>\<^sub>p m)(k \<mapsto> v)\<^sub>p"
  by (transfer, simp)

lemma pdom_antires_insert_notin [simp]:
  "k \<notin> pdom(f) \<Longrightarrow> (- insert k A) \<lhd>\<^sub>p f = (- A) \<lhd>\<^sub>p f"
  by (transfer, auto simp add: restrict_map_def)
 
lemma pdom_res_override [simp]: "A \<lhd>\<^sub>p (f + g) = (A \<lhd>\<^sub>p f) + (A \<lhd>\<^sub>p g)"
  by (simp add: pdom_res_alt_def pfun_override_dist_comp)

lemma pdom_res_minus [simp]: "A \<lhd>\<^sub>p (f - g) = (A \<lhd>\<^sub>p f) - g"
  by (transfer, auto simp add: map_minus_def restrict_map_def)

lemma pdom_res_swap: "(A \<lhd>\<^sub>p f) \<rhd>\<^sub>p B = A \<lhd>\<^sub>p (f \<rhd>\<^sub>p B)"
  by (transfer, auto simp add: restrict_map_def ran_restrict_map_def)

lemma pdom_res_twice [simp]: "A \<lhd>\<^sub>p (B \<lhd>\<^sub>p f) = (A \<inter> B) \<lhd>\<^sub>p f"
  by (transfer, auto simp add: Int_commute)

lemma pdom_res_comp [simp]: "A \<lhd>\<^sub>p (g \<circ>\<^sub>p f) =  g \<circ>\<^sub>p (A \<lhd>\<^sub>p f)"
  by (simp add: pdom_res_alt_def pfun_comp_assoc)

lemma pdom_res_apply [simp]:
  "x \<in> A \<Longrightarrow> (A \<lhd>\<^sub>p f)(x)\<^sub>p = f(x)\<^sub>p"
  by (transfer, auto)

lemma pdom_res_frame_update [simp]: 
  "\<lbrakk> x \<in> pdom(f); (-{x}) \<lhd>\<^sub>p f = (-{x}) \<lhd>\<^sub>p g \<rbrakk> \<Longrightarrow> g(x \<mapsto> f(x)\<^sub>p)\<^sub>p = f"
  by (transfer, auto, metis fun_upd_triv fun_upd_upd restrict_complement_singleton_eq)

lemma pdres_rres_commute: "A \<lhd>\<^sub>p (P \<rhd>\<^sub>p B) = (A \<lhd>\<^sub>p P) \<rhd>\<^sub>p B"
  by (transfer, simp add: map_dres_rres_commute)

lemma pdom_nres_disjoint: "pdom(f) \<inter> A = {} \<Longrightarrow> (- A) \<lhd>\<^sub>p f = f"
  by (metis disjoint_eq_subset_Compl inf.absorb2 pdom_res_pdom pdom_res_twice)

subsection \<open> Range restriction laws \<close>

lemma pran_res_UNIV [simp]: "f \<rhd>\<^sub>p UNIV = f"
  by (transfer, simp add: ran_restrict_map_def)

lemma pran_res_zero [simp]: "{}\<^sub>p \<rhd>\<^sub>p A = {}\<^sub>p"
  by (transfer, auto simp add: ran_restrict_map_def)

lemma pran_res_upd_1 [simp]: "v \<in> A \<Longrightarrow> f(x \<mapsto> v)\<^sub>p \<rhd>\<^sub>p A = (f \<rhd>\<^sub>p A)(x \<mapsto> v)\<^sub>p"
  by (transfer, auto simp add: ran_restrict_map_def)

lemma pran_res_upd_2 [simp]: "v \<notin> A \<Longrightarrow> f(x \<mapsto> v)\<^sub>p \<rhd>\<^sub>p A = ((- {x}) \<lhd>\<^sub>p f) \<rhd>\<^sub>p A"
  by (transfer, auto simp add: ran_restrict_map_def)

lemma pran_res_twice [simp]: "f \<rhd>\<^sub>p A \<rhd>\<^sub>p B = f \<rhd>\<^sub>p (A \<inter> B)"
  by (transfer, simp)

lemma pran_res_alt_def: "f \<rhd>\<^sub>p A = pId_on A \<circ>\<^sub>p f"
  by (transfer, rule ext, auto simp add: ran_restrict_map_def)

lemma pran_res_override: "(f + g) \<rhd>\<^sub>p A \<subseteq>\<^sub>p (f \<rhd>\<^sub>p A) + (g \<rhd>\<^sub>p A)"
  apply (transfer, auto simp add: map_add_def ran_restrict_map_def map_le_def)
  apply (rename_tac f g A a y x)
  apply (case_tac "g a")
   apply (auto)
  done

subsection \<open> Entries \<close>
  
lemma pfun_entries_empty [simp]: "pfun_entries {} f = {}\<^sub>p"
  by (transfer, simp)

lemma pdom_pfun_entries [simp]: "pdom (pfun_entries A f) = A"
  by (transfer, auto)

lemma pran_pfun_entries [simp]: "pran (pfun_entries A f) = f ` A"
  by (transfer, simp add: ran_def, auto)

lemma pfun_entries_apply_1 [simp]: 
  "x \<in> d \<Longrightarrow> (pfun_entries d f)(x)\<^sub>p = f x"
  by (transfer, auto)

lemma pfun_entries_apply_2 [simp]: 
  "x \<notin> d \<Longrightarrow> (pfun_entries d f)(x)\<^sub>p = undefined"
  by (transfer, auto)

lemma pdom_res_entries: "A \<lhd>\<^sub>p pfun_entries B f = pfun_entries (A \<inter> B) f"
  by (transfer, auto simp add: fun_eq_iff restrict_map_def)

lemma pfuse_app [simp]:
  "\<lbrakk> e \<in> pdom F; e \<in> pdom G \<rbrakk> \<Longrightarrow> (pfuse F G)(e)\<^sub>p = (F(e)\<^sub>p, G(e)\<^sub>p)"
  by (metis (no_types, lifting) IntI pfun_entries_apply_1 pfuse_def)

lemma pdom_pfuse [simp]: "pdom (pfuse f g) = pdom(f) \<inter> pdom(g)"
  by (metis (no_types, lifting) pdom_pfun_entries pfuse_def)

subsection \<open> Lambda abstraction \<close>

lemma pabs_cong:
  assumes "A = B" "\<And> x. x \<in> A \<Longrightarrow> P(x) = Q(x)" "\<And> x. x \<in> A \<Longrightarrow> F(x) = G(x)"
  shows "(\<lambda> x \<in> A | P x \<bullet> F(x)) = (\<lambda> x \<in> B | Q x \<bullet> G(x))"
  using assms unfolding pabs_def
  by (transfer, auto simp add: restrict_map_def fun_eq_iff)

lemma pabs_apply [simp]: "\<lbrakk> y \<in> A; P y \<rbrakk>  \<Longrightarrow> (\<lambda> x \<in> A | P x \<bullet> f x) (y)\<^sub>p = f y"
  by (simp add: pabs_def)

lemma pdom_pabs [simp]: "pdom (\<lambda> x \<in> A | P x \<bullet> f x) = A \<inter> Collect P"
  by (simp add: pabs_def)

lemma pran_pabs [simp]: "pran (\<lambda> x \<in> A | P x \<bullet> f x) = {f x | x. x \<in> A \<and> P x}"
  unfolding pabs_def 
  by (transfer, auto simp add: ran_def restrict_map_def)

lemma pabs_eta [simp]: "(\<lambda> x \<in> pdom(f) \<bullet> f(x)\<^sub>p) = f"
  by (simp add: pabs_def, transfer, auto simp add: fun_eq_iff domIff restrict_map_def)

lemma pabs_id [simp]: "(\<lambda> x \<in> A | P x \<bullet> x) = pId_on {x\<in>A. P x}"
  unfolding pabs_def by (transfer, simp add: restrict_map_def)

lemma pfun_entries_pabs: "pfun_entries A f = (\<lambda> x \<in> A \<bullet> f x)"
  by (simp add: pabs_def, transfer, auto)

text \<open> This rule can perhaps be simplified \<close>

lemma pcomp_pabs: 
  "(\<lambda> x \<in> A | P x \<bullet> f x) \<circ>\<^sub>p (\<lambda> x \<in> B | Q x \<bullet> g x) 
    = (\<lambda> x \<in> pdom (pabs B Q g \<rhd>\<^sub>p (A \<inter> Collect P)) \<bullet> (f (g x)))"
  apply (subst pabs_eta[THEN sym, of "(\<lambda> x \<in> A | P x \<bullet> f x) \<circ>\<^sub>p (\<lambda> x \<in> B | Q x \<bullet> g x)"]) 
  apply (simp)
  apply (simp add: pabs_def)
  apply (transfer, auto simp add: restrict_map_def map_comp_def ran_restrict_map_def fun_eq_iff)
  done

subsection \<open> Graph laws \<close>

lemma pfun_graph_inv [code_unfold]: "graph_pfun (pfun_graph f) = f"
  by (transfer, simp)

lemma pfun_eq_graph: "f = g \<longleftrightarrow> pfun_graph f = pfun_graph g"
  by (metis pfun_graph_inv)

lemma Dom_pfun_graph [simp]: "Domain (pfun_graph f) = pdom f"
  by (transfer, simp add: dom_map_graph)

lemma card_pfun_graph [simp]: "finite (pdom f) \<Longrightarrow> card (pfun_graph f) = card (pdom f)"
  by (transfer, simp add: card_map_graph dom_map_graph finite_dom_graph)

lemma pfun_graph_zero: "pfun_graph 0 = {}"
  by (transfer, simp add: map_graph_def)

lemma pfun_graph_pId_on: "pfun_graph (pId_on A) = Id_on A"
  by (transfer, auto simp add: map_graph_def)

lemma pfun_graph_minus: "pfun_graph (f - g) = pfun_graph f - pfun_graph g"
  by (transfer, simp add: map_graph_minus)

lemma pfun_graph_inter: "pfun_graph (f \<inter>\<^sub>p g) = pfun_graph f \<inter> pfun_graph g"
  apply (transfer, auto simp add: map_graph_def)
   apply (metis option.discI)+
  done

lemma pfun_graph_domres: "pfun_graph (A \<lhd>\<^sub>p f) = (A \<lhd>\<^sub>r pfun_graph f)"
  by (transfer, simp add: rel_domres_def map_graph_def restrict_map_def, metis option.simps(3))

lemma pfun_graph_override: "pfun_graph (f + g) = pfun_graph f +\<^sub>r pfun_graph g"
  by (transfer, auto simp add: map_add_def rel_override_def rel_domres_def map_graph_def option.case_eq_if)
     (metis option.collapse)+

lemma pfun_graph_comp: "pfun_graph (f \<circ>\<^sub>p g) = pfun_graph g O pfun_graph f"
  by (transfer, simp add: map_graph_comp)

lemma pfun_graph_pfun_inv: "pfun_inj f \<Longrightarrow> pfun_graph (pfun_inv f) = (pfun_graph f)\<inverse>"
  by (transfer, simp add: map_graph_map_inv)

lemma pfun_graph_pabs: "pfun_graph (\<lambda> x \<in> A | P x \<bullet> f x) = {(x, f x) | x. x \<in> A \<and> P x}"
  unfolding pabs_def
  by (transfer, auto simp add: map_graph_def restrict_map_def)

subsection \<open> Summation \<close>
    
definition pfun_sum :: "('k, 'v::comm_monoid_add) pfun \<Rightarrow> 'v" where
"pfun_sum f = sum (pfun_app f) (pdom f)"
    
lemma pfun_sum_empty [simp]: "pfun_sum {}\<^sub>p = 0"
  by (simp add: pfun_sum_def)

lemma pfun_sum_upd_1:
  assumes "finite(pdom(m))" "k \<notin> pdom(m)"
  shows "pfun_sum (m(k \<mapsto> v)\<^sub>p) = pfun_sum m + v"
  by (simp_all add: pfun_sum_def assms, metis add.commute assms(2) pfun_app_upd_2 sum.cong)

lemma pfun_sums_upd_2:
  assumes "finite(pdom(m))"
  shows "pfun_sum (m(k \<mapsto> v)\<^sub>p) = pfun_sum ((- {k}) \<lhd>\<^sub>p m) + v"
proof (cases "k \<notin> pdom(m)")
  case True
  then show ?thesis 
    by (simp add: pfun_sum_upd_1 assms)
next
  case False
  then show ?thesis
    using assms pfun_sum_upd_1[of "((- {k}) \<lhd>\<^sub>p m)" k v]
    by (simp add: pfun_sum_upd_1)
qed

lemma pfun_sum_dom_res_insert [simp]: 
  assumes "x \<in> pdom f" "x \<notin> A" "finite A" 
  shows "pfun_sum ((insert x A) \<lhd>\<^sub>p f) = f(x)\<^sub>p + pfun_sum (A \<lhd>\<^sub>p f)"
  using assms by (simp add: pfun_sum_def)
  
lemma pfun_sum_pdom_res:
  fixes f :: "('a,'b::ab_group_add) pfun"
  assumes "finite(pdom f)"
  shows "pfun_sum (A \<lhd>\<^sub>p f) = pfun_sum f - (pfun_sum ((- A) \<lhd>\<^sub>p f))"
proof -
  have 1:"A \<inter> pdom(f) = pdom(f) - (pdom(f) - A)"
    by (auto)
  show ?thesis
    apply (simp add: pfun_sum_def)
    apply (subst 1)
    apply (subst sum_diff)
      apply (auto simp add: sum_diff Diff_subset Int_commute boolean_algebra_class.diff_eq assms)
    done
qed
  
lemma pfun_sum_pdom_antires [simp]:
  fixes f :: "('a,'b::ab_group_add) pfun"
  assumes "finite(pdom f)"
  shows "pfun_sum ((- A) \<lhd>\<^sub>p f) = pfun_sum f - pfun_sum (A \<lhd>\<^sub>p f)"
  by (subst pfun_sum_pdom_res, simp_all add: assms)

subsection \<open> Conversions \<close>

definition list_pfun :: "'a list \<Rightarrow> nat \<Rightarrow>\<^sub>p 'a" where
"list_pfun xs = (\<lambda> i | 0 < i \<and> i \<le> length xs \<bullet> xs ! (i-1))"

lemma pdom_list_pfun [simp]: "pdom (list_pfun xs) = {1..length xs}"
  by (auto simp add: list_pfun_def)

lemma pran_list_pfun [simp]: "pran (list_pfun xs) = set xs"
  by (simp add: list_pfun_def, auto)
     (metis One_nat_def Suc_leI diff_Suc_1 in_set_conv_nth zero_less_Suc)

lemma pfun_app_list_pfun: "\<lbrakk> 0 < i; i \<le> length xs \<rbrakk> \<Longrightarrow> (list_pfun xs)(i)\<^sub>p = xs ! (i - 1)"
  by (simp add: list_pfun_def)

lemma pfun_graph_list_pfun: "pfun_graph (list_pfun xs) = (\<lambda> i. (i, xs ! (i - 1))) ` {1..length xs}"
  by (simp add: list_pfun_def pfun_graph_pabs, auto)

lemma range_list_pfun:
  "range list_pfun = {f. \<exists> i. pdom(f) = {1..i}}"
  apply (simp add: list_pfun_def pabs_def)
  apply (transfer, auto)
  apply (rename_tac xs)
  apply (rule_tac x="length xs" in exI, auto simp add: dom_def)[1]
  apply (simp add: image_def)
  apply (rename_tac f i)
  apply (rule_tac x="map (the \<circ> f \<circ> nat) [1..i]" in exI)
  apply (auto simp add: fun_eq_iff restrict_map_def)
  apply (metis Suc_le_mono Suc_pred atLeastAtMost_iff domIff le0 nat_int of_nat_Suc option.exhaust_sel)
  apply (metis One_nat_def atLeastAtMost_iff domIff le_zero_eq zero_neq_one)
  done
  
subsection \<open> Partial Function Lens \<close>

definition pfun_lens :: "'a \<Rightarrow> ('b \<Longrightarrow> ('a, 'b) pfun)" where
[lens_defs]: "pfun_lens i = \<lparr> lens_get = \<lambda> s. s(i)\<^sub>p, lens_put = \<lambda> s v. s(i \<mapsto> v)\<^sub>p \<rparr>"

lemma pfun_lens_mwb [simp]: "mwb_lens (pfun_lens i)"
  by (unfold_locales, simp_all add: pfun_lens_def)

lemma pfun_lens_src: "\<S>\<^bsub>pfun_lens i\<^esub> = {f. i \<in> pdom(f)}"
  by (auto simp add: lens_defs lens_source_def, transfer, force)

lemma lens_override_pfun_lens:
  "x \<in> pdom(g) \<Longrightarrow> f \<oplus>\<^sub>L g on pfun_lens x = f + ({x} \<lhd>\<^sub>p g)"
  by (simp add: lens_defs pfun_ovrd_single_upd)

subsection \<open> Code Generator \<close>

subsubsection \<open> Associative Lists \<close>

lemma relt_pfun_iff: 
  "relt_pfun R f g \<longleftrightarrow> (pdom(f) = pdom(g) \<and> (\<forall> x\<in>pdom(f). R (f(x)\<^sub>p) (g(x)\<^sub>p)))"
  by (transfer, auto simp add: rel_map_iff)

lift_definition pfun_of_alist :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow>\<^sub>p 'b" is map_of .

lemma pfun_of_alist_Nil [simp]: "pfun_of_alist [] = {}\<^sub>p"
  by (transfer, simp)

lemma pfun_of_alist_Cons [simp]: "pfun_of_alist (p # ps) = pfun_of_alist ps(fst p \<mapsto> snd p)\<^sub>p"
  by (transfer, metis (full_types) map_of.simps(2))

lemma dom_pfun_alist [simp, code]: "pdom (pfun_of_alist xs) = set (map fst xs)"
  by (transfer, simp add: dom_map_of_conv_image_fst)

lemma map_graph_map_of: "map_graph (map_of xs) = set (AList.clearjunk xs)"
  apply (induct xs, simp_all)                 
  apply (auto simp add: map_graph_def)
  apply (metis map_of_SomeD map_of_clearjunk map_of_delete)
  apply (metis map_of_SomeD map_of_clearjunk map_of_delete option.inject snd_conv)
  apply (metis clearjunk_delete delete_conv' fun_upd_apply option.distinct(1) weak_map_of_SomeI)
  apply (metis Some_eq_map_of_iff distinct_clearjunk map_of_clearjunk map_of_delete)
  done

lemma pfun_graph_alist [code]: "pfun_graph (pfun_of_alist xs) = set (AList.clearjunk xs)"
  by (transfer, meson map_graph_map_of)

lemma empty_pfun_alist [code]: "{}\<^sub>p = pfun_of_alist []"
  by (transfer, simp)

lemma update_pfun_alist [code]: "pfun_upd (pfun_of_alist xs) k v = pfun_of_alist (AList.update k v xs)"
  by transfer (simp add: update_conv')

lemma apply_pfun_alist [code]: 
  "pfun_app (pfun_of_alist xs) k = (if k \<in> set (map fst xs) then the (map_of xs k) else undefined)"
  apply (transfer, auto)
  apply (metis map_of_eq_None_iff option.distinct(1))
  apply (metis option.distinct(1) weak_map_of_SomeI)
  done

lemma map_of_Cons_code [code]:
  "pfun_lookup (pfun_of_alist []) k = None"
  "pfun_lookup (pfun_of_alist ((l, v) # ps)) k = (if l = k then Some v else map_of ps k)"
  by (transfer, simp)+

lemma map_pfun_alist [code]: 
  "map_pfun f (pfun_of_alist m) = pfun_of_alist (map (\<lambda> (k, v). (k, f v)) m)"
  by (transfer, simp add: map_of_map)

lemma map_pfun_of_map [code]: "map_pfun f (pfun_of_map g) = pfun_of_map (\<lambda> x. map_option f (g x))"
  by (auto simp add: map_pfun_def pfun_of_map_inject fun_eq_iff)

lemma pdom_res_alist [code]:
  "A \<lhd>\<^sub>p (pfun_of_alist m) = pfun_of_alist (AList.restrict A m)"
  by (transfer, simp add: restr_conv')

lemma plus_pfun_alist [code]: "pfun_of_alist f + pfun_of_alist g = pfun_of_alist (g @ f)"
  by (transfer, simp)

lemma pfun_entries_alist [code]: "pfun_entries (set ks) f = pfun_of_alist (map (\<lambda> k. (k, f k)) ks)"
  apply (transfer, auto simp add: fun_eq_iff)
  apply (metis map_of_map_restrict o_def restrict_map_def)
  apply (metis map_of_map_restrict restrict_map_def)
  done

text \<open> Adapted from Mapping theory \<close>

lemma ptabulate_alist [code]: "ptabulate ks f = pfun_of_alist (map (\<lambda>k. (k, f k)) ks)"
  by transfer (simp add: map_of_map_restrict)

lemma pcombine_alist [code]:
  "pcombine f (pfun_of_alist xs) (pfun_of_alist ys) =
     ptabulate (remdups (map fst xs @ map fst ys))
       (\<lambda>x. the (combine_options f (map_of xs x) (map_of ys x)))"
  apply transfer
  apply (rule ext)
  apply (rule sym)
  subgoal for f xs ys x
    apply (cases "map_of xs x"; cases "map_of ys x"; simp)
       apply (force simp: map_of_eq_None_iff combine_options_def option.the_def o_def image_iff
        dest: map_of_SomeD split: option.splits)+
    done
  done

lemma pfun_comp_alist [code]: "pfun_of_alist ys \<circ>\<^sub>p pfun_of_alist xs = pfun_of_alist (AList.compose xs ys)"
  by (transfer, simp add: compose_conv')

lemma equal_pfun [code]:
  "HOL.equal (pfun_of_alist xs) (pfun_of_alist ys) \<longleftrightarrow>
    (let ks = map fst xs; ls = map fst ys
     in (\<forall>l\<in>set ls. l \<in> set ks) \<and> (\<forall>k\<in>set ks. k \<in> set ls \<and> map_of xs k = map_of ys k))"
  apply (simp add: equal_pfun_def, transfer, auto)
  apply (metis map_of_eq_None_iff option.distinct(1) weak_map_of_SomeI)
  apply (metis domI domIff map_of_eq_None_iff weak_map_of_SomeI)
  apply (metis (no_types, lifting) image_iff map_of_eq_None_iff)
  done



lemma set_inter_Collect: "set xs \<inter> Collect P = set (filter P xs)"
  by (auto)

lemma pabs_set [code]: "pabs (set xs) P f = pfun_of_alist (map (\<lambda>k. (k, f k)) (filter P xs))"
  by (simp only: pabs_def pfun_entries_alist pdom_res_entries set_inter_Collect Int_UNIV_right)

text \<open> Hide implementation details for partial functions \<close>

lifting_update pfun.lifting
lifting_forget pfun.lifting

end
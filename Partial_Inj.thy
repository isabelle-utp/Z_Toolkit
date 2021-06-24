section \<open> Partial Injections \<close>

theory Partial_Inj
  imports Partial_Fun
begin

typedef ('a, 'b) pinj = "{f :: ('a, 'b) pfun. pfun_inj f}" 
  morphisms pfun_of_pinj pinj_of_pfun 
  by (auto intro: pfun_inj_empty)

lemma pinj_eq_pfun: "f = g \<longleftrightarrow> pfun_of_pinj f = pfun_of_pinj g"
  by (simp add: pfun_of_pinj_inject)

type_notation pinj (infixr "\<Zpinj>" 1)

setup_lifting type_definition_pinj

lift_definition pinv :: "'a \<Zpinj> 'b \<Rightarrow> 'b \<Zpinj> 'a" is pfun_inv
  by (simp add: pfun_inj_inv)

term pinv

instantiation pinj :: (type, type) zero
begin
  lift_definition zero_pinj :: "('a, 'b) pinj" is "0"
    by simp
instance ..
end

abbreviation pinj_empty :: "('a, 'b) pinj" ("{}\<^sub>\<rho>") where "{}\<^sub>\<rho> \<equiv> 0"

lift_definition pinj_app :: "('a, 'b) pinj \<Rightarrow> 'a \<Rightarrow> 'b" ("_'(_')\<^sub>\<rho>" [999,0] 999) 
is "pfun_app" .

text \<open> Adding a maplet to a partial injection requires that we remove any other maplet that points
  to the value @{term v}, to preserve injectivity. \<close>

lift_definition pinj_upd :: "('a, 'b) pinj \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pinj"
is "\<lambda> f k v. pfun_upd (f \<rhd>\<^sub>p (- {v})) k v"
  by (simp add: pfun_inj_rres pfun_inj_upd)

lift_definition pidom :: "'a \<Zpinj> 'b \<Rightarrow> 'a set" is pdom .

lift_definition piran :: "'a \<Zpinj> 'b \<Rightarrow> 'b set" is pran .

lift_definition pinj_dres :: "'a set \<Rightarrow> ('a, 'b) pinj \<Rightarrow> ('a, 'b) pinj" (infixr "\<lhd>\<^sub>\<rho>" 85) is pdom_res
  by (simp add: pfun_inj_dres)

lift_definition pinj_rres :: "('a, 'b) pinj \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) pinj" (infixl "\<rhd>\<^sub>\<rho>" 85) is pran_res
  by (simp add: pfun_inj_rres)

lift_definition pinj_comp :: "'b \<Zpinj> 'c \<Rightarrow> 'a \<Zpinj> 'b \<Rightarrow> 'a \<Zpinj> 'c" (infixl "\<circ>\<^sub>\<rho>" 55) is "(\<circ>\<^sub>p)"
  by (simp add: pfun_inj_comp)

syntax
  "_PinjUpd"  :: "[('a, 'b) pinj, maplets] => ('a, 'b) pinj" ("_'(_')\<^sub>\<rho>" [900,0]900)
  "_Pinj"     :: "maplets => ('a, 'b) pinj"            ("(1{_}\<^sub>\<rho>)")

translations
  "_PinjUpd m (_Maplets xy ms)"  == "_PinjUpd (_PinjUpd m xy) ms"
  "_PinjUpd m (_maplet  x y)"    == "CONST pinj_upd m x y"
  "_Pinj ms"                     => "_PinjUpd (CONST pempty) ms"
  "_Pinj (_Maplets ms1 ms2)"     <= "_PinjUpd (_Pinj ms1) ms2"
  "_Pinj ms"                     <= "_PinjUpd (CONST pempty) ms"

lemma pinj_app_upd [simp]: "(f(k \<mapsto> v)\<^sub>\<rho>)(x)\<^sub>\<rho> = (if (k = x) then v else (f \<rhd>\<^sub>\<rho> (-{v})) (x)\<^sub>\<rho>)"
  by (transfer, simp)

lemma pinj_eq_iff: "f = g \<longleftrightarrow> (pidom(f) = pidom(g) \<and> (\<forall> x\<in>pidom(f). f(x)\<^sub>\<rho> = g(x)\<^sub>\<rho>))"
  by (transfer, simp add: pfun_eq_iff)

lemma pinv_pempty [simp]: "pinv {}\<^sub>\<rho> = {}\<^sub>\<rho>"
  by (transfer, simp)

lemma pinv_pinj_upd [simp]: "pinv (f(x \<mapsto> y)\<^sub>\<rho>) = (pinv ((-{x}) \<lhd>\<^sub>\<rho> f))(y \<mapsto> x)\<^sub>\<rho>"
  by (transfer, subst pfun_inv_upd, simp_all add: pfun_inj_dres pfun_inj_rres  pfun_inv_rres pdres_rres_commute, simp add: pfun_inv_dres)

lemma pinv_pinv: "pinv (pinv f) = f"
  by (transfer, simp add: pfun_inj_inv_inv)

lemma pinv_pcomp: "pinv (f \<circ>\<^sub>\<rho> g) = pinv g \<circ>\<^sub>\<rho> pinv f"
  by (transfer, simp add: pfun_eq_graph pfun_graph_pfun_inv pfun_graph_comp pfun_inj_comp converse_relcomp)

fun pinj_of_alist :: "('a \<times> 'b) list \<Rightarrow> 'a \<Zpinj> 'b" where
"pinj_of_alist [] = {}\<^sub>\<rho>" |
"pinj_of_alist (p # ps) = (pinj_of_alist ps)(fst p \<mapsto> snd p)\<^sub>\<rho>" 

lemma pinj_empty_alist [code]: "{}\<^sub>\<rho> = pinj_of_alist []"
  by simp

lemma pinj_upd_alist [code]: "(pinj_of_alist xs)(k \<mapsto> v)\<^sub>\<rho> = pinj_of_alist ((k, v) # xs)"
  by simp

context begin

qualified fun clearjunk :: "('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
"clearjunk [] = []" |
"clearjunk (p#ps) = p # filter (\<lambda> (k', v'). k' \<noteq> fst p \<and> v' \<noteq> snd p) (clearjunk ps)"

lemma "pinj_of_alist (clearjunk xs) = pinj_of_alist xs"
  apply (induct xs rule:clearjunk.induct, simp add: pinj_eq_iff, auto simp add: pinj_eq_iff)
  oops

end

declare pinj_of_alist.simps [simp del]

end
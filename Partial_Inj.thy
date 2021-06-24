section \<open> Partial Injections \<close>

theory Partial_Inj
  imports Partial_Fun
begin

typedef ('a, 'b) pinj = "{f :: ('a, 'b) pfun. pfun_inj f}" 
  morphisms pfun_of_pinj pinj_of_pfun 
  by (auto intro: pfun_inj_empty)

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

lift_definition pinj_upd :: "('a, 'b) pinj \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pinj"
is "\<lambda> f k v. pfun_upd (f \<rhd>\<^sub>p (- {v})) k v"
  by (simp add: pfun_inj_rres pfun_inj_upd)

lift_definition pinj_dres :: "'a set \<Rightarrow> ('a, 'b) pinj \<Rightarrow> ('a, 'b) pinj" (infixr "\<lhd>\<^sub>\<rho>" 85) is pdom_res
  by (simp add: pfun_inj_dres)

lift_definition pinj_rres :: "('a, 'b) pinj \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) pinj" (infixl "\<rhd>\<^sub>\<rho>" 85) is pran_res
  by (simp add: pfun_inj_rres)

(*
instantiation pinj :: (type, type) plus
begin
lift_definition plus_pinj :: "'a \<Zpinj> 'b \<Rightarrow> 'a \<Zpinj> 'b \<Rightarrow> 'a \<Zpinj> 'b" is "\<lambda> f g. (f \<rhd>\<^sub>p (- pran(g))) + g" 
*)

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
  
lemma pinv_pinv: "pinv (pinv f) = f"
  by (transfer, simp add: pfun_inj_inv_inv)

fun pinj_of_alist :: "('a \<times> 'b) list \<Rightarrow> 'a \<Zpinj> 'b" where
"pinj_of_alist [] = {}\<^sub>\<rho>" |
"pinj_of_alist ((k, v) # m) = (pinj_of_alist m)(k \<mapsto> v)\<^sub>\<rho>" 

hide_fact pinj_of_alist.simps


end
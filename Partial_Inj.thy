theory Partial_Inj
  imports Partial_Fun
begin

typedef ('a, 'b) pinj = "{f :: ('a, 'b) pfun. pfun_inj f}" 
  morphisms pfun_of_pinj pinj_of_pfun 
  by (auto intro: pfun_inj_empty)

setup_lifting type_definition_pinj

lift_definition pinv :: "('a, 'b) pinj \<Rightarrow> ('b, 'a) pinj" is pfun_inv
  by (simp add: pfun_inj_inv)

instantiation pinj :: (type, type) zero
begin
  lift_definition zero_pinj :: "('a, 'b) pinj" is "0"
    by simp
instance ..
end

lift_definition pinj_upd :: "('a, 'b) pinj \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pinj"
is "\<lambda> f k v. if (v \<in> pran f) then f else pfun_upd f k v"
  by (auto simp add: pfun_inj_upd)

lemma pinv_pinv: "pinv (pinv f) = f"
  by (transfer, simp add: pfun_inj_inv_inv)

end
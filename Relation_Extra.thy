section \<open> Relational Universe \<close>

theory Relation_Extra
  imports "HOL-Library.FuncSet"
begin

text \<open> This theory develops a universe for a Z-like relational language, including the core 
  operators of the ISO Z metalanguage. Much of this already exists in @{theory HOL.Relation},
  but we need to add some additional functions and sets. It characterises relations, partial
  functions, total functions, and finite functions. \<close>

subsection \<open> Type Syntax\<close>

text \<open> We set up some nice syntax for heterogeneous relations at the type level \<close>

syntax
  "_rel_type" :: "type \<Rightarrow> type \<Rightarrow> type" (infixr "\<leftrightarrow>" 0)

translations
  (type) "'a \<leftrightarrow> 'b" == (type) "('a \<times> 'b) set"

subsection \<open> Notation for types as sets \<close>

definition "TUNIV (a::'a itself) = (UNIV :: 'a set)"

syntax "_tvar" :: "type \<Rightarrow> logic" ("[_]\<^sub>T")
translations "['a]\<^sub>T" == "CONST TUNIV TYPE('a)"

lemma TUNIV_mem [simp]: "x \<in> ['a]\<^sub>T"
  by (simp add: TUNIV_def)

subsection \<open> Relational Function Operations \<close>

text \<open> These functions are all adapted from their ISO Z counterparts. \<close>

definition rel_apply :: "('a \<leftrightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("_'(_')\<^sub>r" [999,0] 999) where
"rel_apply R x = (if x \<in> Domain(R) then THE y. (x, y) \<in> R else undefined)"

text \<open> If there exists a unique @{term "e\<^sub>3"} such that @{term "(e\<^sub>2, e\<^sub>3)"} is in @{term "e\<^sub>1"}, then 
  the value of @{term "e\<^sub>1(e\<^sub>2)\<^sub>r"} is @{term e\<^sub>3}, otherwise each @{term "e\<^sub>1(e\<^sub>2)\<^sub>r"} has a fixed but 
  unknown value (i.e. @{const undefined}). \<close>

definition rel_domres :: "'a set \<Rightarrow> ('a \<leftrightarrow> 'b) \<Rightarrow> 'a \<leftrightarrow> 'b" (infixr "\<lhd>\<^sub>r" 85) where
"rel_domres A R = {(k, v) \<in> R. k \<in> A}"

text \<open> Domain restriction (@{term "A \<lhd>\<^sub>r R"} contains the set of pairs in @{term R}, such that the
  first element of every such pair in in @{term A}. \<close>

definition rel_override :: "('a \<leftrightarrow> 'b) \<Rightarrow> ('a \<leftrightarrow> 'b) \<Rightarrow> 'a \<leftrightarrow> 'b" (infixl "+\<^sub>r" 65) where
"rel_override R S = ((- Domain S) \<lhd>\<^sub>r R) \<union> S"

text \<open> Relational override (@{term "R +\<^sub>r S"}) combines the pairs of @{term S} with the pairs of
  @{term S} that do not have a first element also in @{term S}. \<close>

definition rel_update :: "('a \<leftrightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<leftrightarrow> 'b" where
"rel_update R k v = rel_override R {(k, v)}"

text \<open> Relational update adds a new pair to a relation. \<close>

definition rel_compat :: "('a \<leftrightarrow> 'b) \<Rightarrow> ('a \<leftrightarrow> 'b) \<Rightarrow> bool" (infix "\<approx>\<^sub>r" 50) where
"R \<approx>\<^sub>r S \<longleftrightarrow> (Domain R) \<lhd>\<^sub>r S = (Domain S) \<lhd>\<^sub>r R"

text \<open> Relations are compatible is they agree on the values for maplets they both possess. \<close>

subsection \<open> Domain laws \<close>

lemma Domain_Preimage: "Domain P = P\<inverse> `` UNIV"
  by (simp add: Image_def Domain_unfold)

lemma Domain_relcomp: "Domain (P O Q) = (P\<inverse> `` Domain(Q))"
  by (simp add: Domain_Preimage converse_relcomp relcomp_Image)

subsection \<open> Range laws \<close>

lemma Range_Image: "Range P = P `` UNIV"
  by (simp add: Image_def Range_iff set_eq_iff)

lemma Range_relcomp: "Range (P O Q) = (Q `` Range(P))"
  by (simp add: Range_Image relcomp_Image)

subsection \<open> Domain Restriction \<close>

lemma Domain_rel_domres [simp]: "Domain (A \<lhd>\<^sub>r R) = A \<inter> Domain(R)"
  by (auto simp add: rel_domres_def)

lemma rel_domres_empty [simp]: "{} \<lhd>\<^sub>r R = {}"
  by (simp add: rel_domres_def)

lemma rel_domres_UNIV [simp]: "UNIV \<lhd>\<^sub>r R = R"
  by (simp add: rel_domres_def)

lemma rel_domres_nil [simp]: "A \<lhd>\<^sub>r {} = {}"
  by (simp add: rel_domres_def)

lemma rel_domres_inter [simp]: "A \<lhd>\<^sub>r B \<lhd>\<^sub>r R = (A \<inter> B) \<lhd>\<^sub>r R"
  by (auto simp add: rel_domres_def)

lemma rel_domres_compl_disj: "A \<inter> Domain P = {} \<Longrightarrow> (- A) \<lhd>\<^sub>r P = P"
  by (auto simp add: rel_domres_def)

lemma rel_domres_Id_on: "A \<lhd>\<^sub>r R = Id_on A O R"
  by (auto simp add: rel_domres_def Id_on_def relcomp_unfold)

subsection \<open> Relational Override \<close>

interpretation rel_override_monoid: monoid_add "(+\<^sub>r)" "{}"
  by (unfold_locales, simp_all add: rel_override_def, auto simp add: rel_domres_def)

lemma rel_override_idem [simp]: "P +\<^sub>r P = P"
  by (auto simp add: rel_override_def rel_domres_def)

lemma Domain_rel_override [simp]: "Domain (R +\<^sub>r S) = Domain(R) \<union> Domain(S)"
  by (auto simp add: rel_override_def Domain_Un_eq)

lemma Range_rel_override: "Range(R +\<^sub>r S) \<subseteq> Range(R) \<union> Range(S)"
  by (auto simp add: rel_override_def rel_domres_def)

subsection \<open> Functional Relations \<close>

abbreviation functional :: "('a \<leftrightarrow> 'b) \<Rightarrow> bool" where
"functional R \<equiv> single_valued R"

lemma functional_def: "functional R \<longleftrightarrow> inj_on fst R"
  by (force simp add: single_valued_def inj_on_def)

lemma functional_algebraic: "functional R \<longleftrightarrow> R\<inverse> O R \<subseteq> Id"
  apply (auto simp add: functional_def subset_iff relcomp_unfold)
  using inj_on_eq_iff apply fastforce
  apply (metis inj_onI surjective_pairing)
  done

lemma functional_apply: 
  assumes "functional R" "(x, y) \<in> R"
  shows "R(x)\<^sub>r = y"
  by (metis (no_types, lifting) Domain.intros DomainE assms(1) assms(2) single_valuedD rel_apply_def theI_unique)  

lemma functional_elem:
  assumes "functional R" "x \<in> Domain(R)"
  shows "(x, R(x)\<^sub>r) \<in> R"
  using assms(1) assms(2) functional_apply by fastforce

lemma functional_override [intro]: "\<lbrakk> functional R; functional S \<rbrakk> \<Longrightarrow> functional (R +\<^sub>r S)"
  by (auto simp add: functional_algebraic rel_override_def rel_domres_def)

definition functional_list :: "('a \<times> 'b) list \<Rightarrow> bool" where
"functional_list xs = (\<forall> x y z. ListMem (x,y) xs \<and> ListMem (x,z) xs \<longrightarrow> y = z)"

lemma functional_insert [simp]: "functional (insert (x,y) g) \<longleftrightarrow> (g``{x} \<subseteq> {y} \<and> functional g)"
  by (auto simp add:functional_def inj_on_def image_def)

lemma functional_list_nil[simp]: "functional_list []"
  by (simp add:functional_list_def ListMem_iff)

lemma functional_list: "functional_list xs \<longleftrightarrow> functional (set xs)"
  apply (induct xs)
   apply (simp add:functional_def)
  apply (simp add:functional_def functional_list_def ListMem_iff)
  apply (safe)
         apply (force)
        apply (force)
       apply (force)
      apply (force)
     apply (force)
    apply (force)
   apply (force)
  apply (force)
  done

definition fun_rel :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<leftrightarrow> 'b)" where
"fun_rel f = {(x, y). y = f x}"

lemma functional_fun_rel: "functional (fun_rel f)"
  by (simp add: fun_rel_def functional_def)
     (metis (mono_tags, lifting) Product_Type.Collect_case_prodD inj_onI prod.expand)

lemma rel_apply_fun [simp]: "(fun_rel f)(x)\<^sub>r = f x"
  by (simp add: fun_rel_def rel_apply_def)

subsection \<open> Left-Total Relations\<close>

definition left_totalr_on :: "'a set \<Rightarrow> ('a \<leftrightarrow> 'b) \<Rightarrow> bool" where
"left_totalr_on A R \<longleftrightarrow> (\<forall>x\<in>A. \<exists>y. (x, y) \<in> R)"

abbreviation "left_totalr R \<equiv> left_totalr_on UNIV R"

lemma left_totalr_algebraic: "left_totalr R \<longleftrightarrow> Id \<subseteq> R O R\<inverse>"
  by (auto simp add: left_totalr_on_def)

lemma left_totalr_fun_rel: "left_totalr (fun_rel f)"
  by (simp add: left_totalr_on_def fun_rel_def)

subsection \<open> Relation Sets \<close>

definition rel_typed :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<leftrightarrow> 'b) set" (infixr "\<leftrightarrow>" 55) where
"rel_typed A B = {R. Domain(R) \<subseteq> A \<and> Range(R) \<subseteq> B}" \<comment> \<open> Relations \<close>

lemma rel_typed_intro: "\<lbrakk> Domain(R) \<subseteq> A; Range(R) \<subseteq> B \<rbrakk> \<Longrightarrow> R \<in> A \<leftrightarrow> B"
  by (simp add: rel_typed_def)

definition rel_pfun :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<leftrightarrow> 'b) set" (infixr "\<rightarrow>\<^sub>p" 55) where
"rel_pfun A B = {R. R \<in> A \<leftrightarrow> B \<and> functional R}" \<comment> \<open> Partial Functions \<close>

lemma rel_pfun_intro: "\<lbrakk> R \<in> A \<leftrightarrow> B; functional R \<rbrakk> \<Longrightarrow> R \<in> A \<rightarrow>\<^sub>p B"
  by (simp add: rel_pfun_def)

definition rel_tfun :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<leftrightarrow> 'b) set" (infixr "\<rightarrow>\<^sub>t" 55) where
"rel_tfun A B = {R. R \<in> A \<rightarrow>\<^sub>p B \<and> left_totalr R}" \<comment> \<open> Total Functions \<close>

definition rel_ffun :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<leftrightarrow> 'b) set" (infixr "\<rightarrow>\<^sub>f" 55) where
"rel_ffun A B = {R. R \<in> A \<rightarrow>\<^sub>p B \<and> finite(Domain R)}" \<comment> \<open> Finite Functions \<close>

subsection \<open> Closure Properties \<close>

text \<open> These can be seen as typing rules for relational functions \<close>

named_theorems rclos

lemma rel_ffun_is_pfun [rclos]: "R \<in> rel_ffun A B \<Longrightarrow> R \<in> A \<rightarrow>\<^sub>p B"
  by (simp add: rel_ffun_def)

lemma rel_tfun_is_pfun [rclos]: "R \<in> A \<rightarrow>\<^sub>t B \<Longrightarrow> R \<in> A \<rightarrow>\<^sub>p B"
  by (simp add: rel_tfun_def)

lemma rel_pfun_is_typed [rclos]: "R \<in> A \<rightarrow>\<^sub>p B \<Longrightarrow> R \<in> A \<leftrightarrow> B"
  by (simp add: rel_pfun_def)

lemma rel_ffun_empty [rclos]: "{} \<in> rel_ffun A B"
  by (simp add: rel_ffun_def rel_pfun_def rel_typed_def)

lemma rel_pfun_apply [rclos]: "\<lbrakk> x \<in> Domain(R); R \<in> A \<rightarrow>\<^sub>p B \<rbrakk> \<Longrightarrow> R(x)\<^sub>r \<in> B"
  using functional_apply by (fastforce simp add: rel_pfun_def rel_typed_def)

lemma rel_tfun_apply [rclos]: "\<lbrakk> x \<in> A; R \<in> A \<rightarrow>\<^sub>t B \<rbrakk> \<Longrightarrow> R(x)\<^sub>r \<in> B"
  by (metis (no_types, lifting) Domain_iff iso_tuple_UNIV_I left_totalr_on_def mem_Collect_eq rel_pfun_apply rel_tfun_def)

lemma rel_typed_insert [rclos]: "\<lbrakk> R \<in> A \<leftrightarrow> B; x \<in> A; y \<in> B \<rbrakk> \<Longrightarrow> insert (x, y) R \<in> A \<leftrightarrow> B"
  by (simp add: rel_typed_def)

lemma rel_pfun_insert [rclos]: "\<lbrakk> R \<in> A \<rightarrow>\<^sub>p B; x \<in> A; y \<in> B; x \<notin> Domain(R) \<rbrakk> \<Longrightarrow> insert (x, y) R \<in> A \<rightarrow>\<^sub>p B"
  by (auto intro: rclos simp add: rel_pfun_def)

lemma rel_pfun_override [rclos]: "\<lbrakk> R \<in> A \<rightarrow>\<^sub>p B; S \<in> A \<rightarrow>\<^sub>p B \<rbrakk> \<Longrightarrow> (R +\<^sub>r S) \<in> A \<rightarrow>\<^sub>p B"
  apply (rule rel_pfun_intro)
   apply (rule rel_typed_intro)
  apply (auto simp add: rel_pfun_def rel_typed_def)
  apply (metis (no_types, hide_lams) Range.simps Range_Un_eq Range_rel_override Un_iff rev_subsetD)
  done

end
section \<open> Sequences \<close>

theory Sequence_Toolkit
  imports Number_Toolkit
begin

subsection \<open> Conversion \<close>

text \<open> We define a number of coercions for mapping a list to finite function. \<close>

abbreviation rel_of_list :: "'a list \<Rightarrow> nat \<leftrightarrow> 'a" where
"rel_of_list xs \<equiv> pfun_graph (list_pfun xs)"

abbreviation seq_nth ("_'(_')\<^sub>s" [999,0] 999) where
"seq_nth xs i \<equiv> xs ! (i - 1)"

declare [[coercion list_ffun]]
declare [[coercion list_pfun]]
declare [[coercion rel_of_list]]
declare [[coercion seq_nth]]

subsection \<open> Number range\<close>

lemma number_range: "{i..j} = {k :: \<int>. i \<le> k \<and> k \<le> j}"
  by (auto)

text \<open> The number range from $i$ to $j$ is the set of all integers greater than or equal to $i$, 
  which are also less than or equal to $j$.\<close>

subsection \<open> Iteration \<close>

definition iter :: "\<int> \<Rightarrow> ('X \<leftrightarrow> 'X) \<Rightarrow> ('X \<leftrightarrow> 'X)" where
"iter n R = (if (n \<ge> 0) then R ^^ (nat n) else (R\<^sup>\<sim>) ^^ (nat n))"

lemma iter_eqs:
  "iter 0 r = Id"
  "n \<ge> 0 \<Longrightarrow> iter (n + 1) r = r \<^bold>; (iter n r)"
  "n < 0 \<Longrightarrow> iter (n + 1) r = iter n (r\<^sup>\<sim>)"
  by (simp_all add: iter_def, metis Suc_nat_eq_nat_zadd1 add.commute relpow.simps(2) relpow_commute)

subsection \<open> Number of members of a set \<close>

notation card ("#_" [999] 999)

lemma card_rel_of_list [simp]: 
  "#(rel_of_list xs) = length xs"
  by (auto simp add: pfun_graph_list_pfun card_image inj_on_convol_ident)

subsection \<open> Maximum \<close>

subsection \<open> Minimum \<close>

subsection \<open> Finite sequences \<close>

definition "seq X = {f \<in> \<nat> \<rightarrow>\<^sub>f X. dom f = {1..#f}}"

lemma seq_ffun_set: "range list_ffun = {f :: \<nat> \<Rightarrow>\<^sub>f 'X. dom(f) = {1..#f}}"
  by (simp add: range_list_ffun, force)

lemma seq_eq: "range (rel_of_list :: 'a list \<Rightarrow> nat \<leftrightarrow> 'a) = seq (UNIV :: 'a set)"
  oops

subsection \<open> Non-empty finite sequences \<close>

definition "seq\<^sub>1 X = seq X - {{}}"

subsection \<open> Head of a sequence \<close>

definition head :: "'a list \<Rightarrow>\<^sub>p 'a" where
"head = {xs. length xs > 0} \<lhd> fun_pfun hd"

lemma dom_head: "dom head = {xs. length xs > 0}"
  by (simp add: head_def)

lemma head_app: "length xs > 0 \<Longrightarrow> head xs = hd xs"
  by (simp add: head_def)

subsection \<open> Last of a sequence \<close>

lemma last_eq: "length s > 0 \<Longrightarrow> last s = s (#s)"
  by (simp add: last_conv_nth)


end
section \<open> Sequence Toolkit \<close>

theory Sequence_Toolkit
  imports Number_Toolkit
begin

subsection \<open> Conversion \<close>

text \<open> We define a number of coercions for mapping a list to finite function. \<close>

abbreviation rel_of_list :: "'a list \<Rightarrow> nat \<leftrightarrow> 'a" ("\<lbrakk>_\<rbrakk>\<^sub>s") where
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

notation size ("#_" [999] 999)

instantiation set :: (type) size
begin
definition [simp]: "size A = card A"
instance ..
end

lemma size_rel_of_list: 
  "#xs = length xs" 
  by simp

subsection \<open> Minimum \<close>

text \<open> Implemented by the function @{const Min}. \<close>

subsection \<open> Maximum \<close>

text \<open> Implemented by the function @{const Max}. \<close>

subsection \<open> Finite sequences \<close>

definition "seq (a::'a itself) = lists (UNIV :: 'a set)"

syntax "_seq" :: "type \<Rightarrow> logic" ("seq'(_')")
translations "seq('a)" == "CONST seq TYPE('a)"

lemma seq_ffun_set: "range list_ffun = {f :: \<nat> \<Rightarrow>\<^sub>f 'X. dom(f) = {1..#f}}"
  by (simp add: range_list_ffun, force)

subsection \<open> Non-empty finite sequences \<close>

definition "seq1 X = seq X - {[]}"

syntax "_seq1" :: "type \<Rightarrow> logic" ("seq\<^sub>1'(_')")
translations "seq\<^sub>1('a)" == "CONST seq1 TYPE('a)"

lemma seq1 [simp]: "xs \<in> seq\<^sub>1('a) \<Longrightarrow> #xs > 0"
  by (simp add: seq1_def)

subsection \<open> Injective sequences \<close>

definition "iseq X = seq X \<inter> Collect distinct"

syntax "_iseq" :: "type \<Rightarrow> logic" ("iseq'(_')")
translations "iseq('a)" == "CONST iseq TYPE('a)"

(* Proof that this corresponds to the Z definition required *)

subsection \<open> Sequence brackets \<close>

text \<open> Provided by the HOL list notation @{term "[x, y, z]"}. \<close>

subsection \<open> Concatenation \<close>

text \<open> Provided by the HOL concatenation operator @{term "(@)"}. \<close>

subsection \<open> Reverse \<close>

text \<open> Provided by the HOL function @{const rev}. \<close>

subsection \<open> Head of a sequence \<close>

definition head :: "'a list \<Rightarrow>\<^sub>p 'a" where
"head = (\<lambda> xs :: 'a list | #xs > 0 \<bullet> hd xs)"

lemma dom_head: "dom head = {xs. #xs > 0}"
  by (simp add: head_def)

lemma head_app: "#xs > 0 \<Longrightarrow> head xs = hd xs"
  by (simp add: head_def)

lemma head_z_def: "xs \<in> seq\<^sub>1('a) \<Longrightarrow> head xs = xs 1"
  by (simp add: hd_conv_nth head_app seq1_def)

subsection \<open> Last of a sequence \<close>

hide_const (open) last

definition last :: "'a list \<Rightarrow>\<^sub>p 'a" where
"last = (\<lambda> xs :: 'a list | #xs > 0 \<bullet> List.last xs)"

lemma dom_last: "dom last = {xs. #xs > 0}"
  by (simp add: last_def)

lemma last_app: "#xs > 0 \<Longrightarrow> last xs = List.last xs"
  by (simp add: last_def)

lemma last_eq: "#s > 0 \<Longrightarrow> last s = s (#s)"
  by (simp add: last_app last_conv_nth)

subsection \<open> Tail of a sequence \<close>

definition tail :: "'a list \<Rightarrow>\<^sub>p 'a list" where
"tail = (\<lambda> xs :: 'a list | #xs > 0 \<bullet> tl xs)"

lemma dom_tail: "dom tail = {xs. #xs > 0}"
  by (simp add: tail_def)

lemma tail_app: "#xs > 0 \<Longrightarrow> tail xs = tl xs"
  by (simp add: tail_def)

subsection \<open> Examples \<close>

lemma "([1,2,3] \<^bold>; (\<lambda> x \<bullet> x + 1)) 1 = 2"
  by (simp add: pfun_graph_comp[THEN sym] list_pfun_def pcomp_pabs)

end
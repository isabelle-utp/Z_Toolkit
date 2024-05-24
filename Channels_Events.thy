section \<open> Channels and Events \<close>

theory Channels_Events
  imports "Optics.Optics" "Relation_Toolkit"
begin

subsection \<open> Event Syntax \<close>

definition evsimple :: "(unit \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'e" where
[code_unfold]: "evsimple c = build\<^bsub>c\<^esub> ()"

definition evparam :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'a \<Rightarrow> 'e" where
[code_unfold]: "evparam c v = build\<^bsub>c\<^esub> v"

nonterminal evt

syntax 
  "_evt_id"    :: "id \<Rightarrow> evt" ("_")
  "_evt_param" :: "id \<Rightarrow> logic \<Rightarrow> evt" ("_/ _")

translations 
  "_evt_id x" == "CONST evsimple x"
  "_evt_param x v" == "CONST evparam x v"

subsection \<open> Channel Sets \<close>

definition csbasic :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'e set" where
[code_unfold]: "csbasic c = range (build\<^bsub>c\<^esub>)"

definition cscollect :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'e set" where
[code_unfold]: "cscollect c A P = {build\<^bsub>c\<^esub> v | v. v \<in> A \<and> P v}"

definition csinsert :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'e set \<Rightarrow> 'e set" where
[code_unfold]: "csinsert e E = csbasic e \<union> E"

definition csempty ("\<lbrace>\<rbrace>") where [code_unfold]: "\<lbrace>\<rbrace> = {}"

nonterminal chan and chans

syntax 
  "_chan"          :: "id \<Rightarrow> chans" ("_")
  "_chans"         :: "id \<Rightarrow> chans \<Rightarrow> chans" ("_,/ _")
  "_ch_enum"       :: "chans \<Rightarrow> logic" ("\<lbrace>_\<rbrace>")
  "_ch_collect"    :: "id \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<lbrace>_/ _ \<in> _./ _\<rbrace>")
  "_ch_collect_ns" :: "id \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<lbrace>_/ _./ _\<rbrace>")

translations 
  "_chan c" => "CONST csbasic c"
  "_chans e es" => "CONST csinsert e es"
  "_ch_enum A" => "A"
  "_ch_enum (_chan c)" <= "CONST csbasic c"
  "_ch_enum (_chans c cs)" <= "CONST csinsert c (_ch_enum cs)"
  "_ch_collect e x A P" == "CONST cscollect e A (\<lambda> x. P)"
  "_ch_collect_ns e x P" == "_ch_collect e x (CONST UNIV) P"

subsection \<open> Renaming Relations \<close>

definition rncollect :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e\<^sub>1) \<Rightarrow> ('b \<Longrightarrow>\<^sub>\<triangle> 'e\<^sub>2) \<Rightarrow> 'c set \<Rightarrow> ('c \<Rightarrow> ('a \<times> 'b) \<times> bool) \<Rightarrow> 'e\<^sub>1 \<leftrightarrow> 'e\<^sub>2" where
"rncollect c\<^sub>1 c\<^sub>2 A f = {(build\<^bsub>c\<^sub>1\<^esub> (fst (fst (f x))), build\<^bsub>c\<^sub>2\<^esub> (snd (fst (f x)))) | x. x \<in> A \<and> snd (f x)}"
 
syntax 
  "_rncollect"    :: "evt \<Rightarrow> evt \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<lbrace>_ \<mapsto> _ | _ \<in> _./ _\<rbrace>")
  "_rncollect_ns" :: "evt \<Rightarrow> evt \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<lbrace>_ \<mapsto> _ | _./ _\<rbrace>")

translations 
  "_rncollect (_evt_param c\<^sub>1 v\<^sub>1) (_evt_param c\<^sub>2 v\<^sub>2) x A P" == "CONST rncollect c\<^sub>1 c\<^sub>2 A (\<lambda> x. ((v\<^sub>1, v\<^sub>2), P))"
  "_rncollect (_evt_id c\<^sub>1) (_evt_param c\<^sub>2 v\<^sub>2) x A P" == "CONST rncollect c\<^sub>1 c\<^sub>2 A (\<lambda> x. (((), v\<^sub>2), P))"
  "_rncollect (_evt_param c\<^sub>1 v\<^sub>1) (_evt_id c\<^sub>2) x A P" == "CONST rncollect c\<^sub>1 c\<^sub>2 A (\<lambda> x. ((v\<^sub>1, ()), P))"
  "_rncollect (_evt_id c\<^sub>1) (_evt_id c\<^sub>2) x A P" == "CONST rncollect c\<^sub>1 c\<^sub>2 A (\<lambda> x. (((), ()), P))"
  "_rncollect_ns e\<^sub>1 e\<^sub>2 x P" == "_rncollect e\<^sub>1 e\<^sub>2 x (CONST UNIV) P"

end
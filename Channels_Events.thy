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

subsection \<open> Channel Partial Instantiation \<close>

text \<open> Create a new reduced channel (prism) by instantiating and fixing the first parameter of an 
  existing channel. \<close>

definition chinst :: "('a \<times> 'b \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'a \<Rightarrow> ('b \<Longrightarrow>\<^sub>\<triangle> 'e)" where
"chinst c a = \<lparr> prism_match = (\<lambda> e. case match\<^bsub>c\<^esub> e of 
                                       None \<Rightarrow> None 
                                     | Some (a', b') \<Rightarrow> if (a = a') then Some b' else None) 
               , prism_build = (\<lambda> b. build\<^bsub>c\<^esub> (a, b)) \<rparr>"     

lemma chinst_wb_prism [simp]: "wb_prism c \<Longrightarrow> wb_prism (chinst c a)"
  by (simp add: chinst_def, unfold_locales, auto simp add: option.case_eq_if)

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
  "_chan_id"       :: "id \<Rightarrow> chan" ("_")
  "_chan_inst"     :: "chan \<Rightarrow> id \<Rightarrow> chan" ("_\<cdot>_" [100,101] 101)
  "_chan"          :: "chan \<Rightarrow> chans" ("_")
  "_chans"         :: "chan \<Rightarrow> chans \<Rightarrow> chans" ("_,/ _")
  "_ch_enum"       :: "chans \<Rightarrow> logic" ("\<lbrace>_\<rbrace>")
  "_ch_collect"    :: "id \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<lbrace>_/ _ \<in> _./ _\<rbrace>")
  "_ch_collect_ns" :: "id \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<lbrace>_/ _./ _\<rbrace>")

translations
  "_chan_id c" => "c"
  "_chan_inst c x" => "CONST chinst c x" 
  "_chan c" => "CONST csbasic c"
  "_chans e es" => "CONST csinsert e es"
  "_ch_enum A" => "A"
  "_ch_enum (_chan c)" <= "CONST csbasic c"
  "_chan (_chan_inst c x)" <= "_chan (CONST chinst c x)"
  "_chan_inst (_chan_inst c x) y" <= "_chan_inst (CONST chinst c x) y"
  "_ch_enum (_chans c cs)" <= "CONST csinsert c (_ch_enum cs)"
  "_ch_collect e x A P" == "CONST cscollect e A (\<lambda> x. P)"
  "_ch_collect_ns e x P" == "_ch_collect e x (CONST UNIV) P"

subsection \<open> Renaming Relations \<close>

nonterminal chexpr and chargs and rnenum

definition rnsingle :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e\<^sub>1) \<Rightarrow> ('a \<Longrightarrow>\<^sub>\<triangle> 'e\<^sub>2) \<Rightarrow> 'e\<^sub>1 \<leftrightarrow> 'e\<^sub>2" where
"rnsingle c\<^sub>1 c\<^sub>2 = {(build\<^bsub>c\<^sub>1\<^esub> v, build\<^bsub>c\<^sub>2\<^esub> v) | v. True}" 

definition rninsert :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e\<^sub>1) \<Rightarrow> ('a \<Longrightarrow>\<^sub>\<triangle> 'e\<^sub>2) \<Rightarrow> ('e\<^sub>1 \<leftrightarrow> 'e\<^sub>2) \<Rightarrow> 'e\<^sub>1 \<leftrightarrow> 'e\<^sub>2" where
"rninsert c\<^sub>1 c\<^sub>2 rn = rnsingle c\<^sub>1 c\<^sub>2 \<union> rn"  

definition rncollect :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e\<^sub>1) \<Rightarrow> ('b \<Longrightarrow>\<^sub>\<triangle> 'e\<^sub>2) \<Rightarrow> 'c set \<Rightarrow> ('c \<Rightarrow> ('a \<times> 'b) \<times> bool) \<Rightarrow> 'e\<^sub>1 \<leftrightarrow> 'e\<^sub>2" where
"rncollect c\<^sub>1 c\<^sub>2 A f = {(build\<^bsub>c\<^sub>1\<^esub> (fst (fst (f x))), build\<^bsub>c\<^sub>2\<^esub> (snd (fst (f x)))) | x. x \<in> A \<and> snd (f x)}"

syntax
  "_rnsingle"      :: "chexpr \<Rightarrow> chexpr \<Rightarrow> rnenum" ("_ \<mapsto> _")
  "_rnmaplets"     :: "chexpr \<Rightarrow> chexpr \<Rightarrow> rnenum \<Rightarrow> rnenum" ("_ \<mapsto> _,/ _")
  "_rnenum"        :: "rnenum \<Rightarrow> logic" ("\<lbrace>_\<rbrace>")
  "_charg"        :: "logic \<Rightarrow> chargs" ("_")
  "_chargs"       :: "logic \<Rightarrow> chargs \<Rightarrow> chargs" ("_\<cdot>_" [65,66] 66) 
  "_chid"         :: "id \<Rightarrow> chexpr" ("_")
  "_chinst"       :: "id \<Rightarrow> chargs \<Rightarrow> chexpr" ("_\<cdot>_" [65,66] 66)
  "_rncollect"    :: "evt \<Rightarrow> evt \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<lbrace>_ \<mapsto> _ | _ \<in> _./ _\<rbrace>")
  "_rncollect_ns" :: "evt \<Rightarrow> evt \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<lbrace>_ \<mapsto> _ | _./ _\<rbrace>")

translations
  "_chid c" => "c"
  "_chinst c (_charg x)" == "CONST chinst c x"
  "_chinst c (_chargs x y)" == "_chinst (CONST chinst c x) y" 

  "_rnenum A" => "A"
  "_rnsingle c\<^sub>1 c\<^sub>2" => "CONST rnsingle c\<^sub>1 c\<^sub>2"
  "_rnmaplets c\<^sub>1 c\<^sub>2 r" => "CONST rninsert c\<^sub>1 c\<^sub>2 r"
  "_rnenum (_rnsingle c\<^sub>1 c\<^sub>2)" <= "CONST rnsingle c\<^sub>1 c\<^sub>2"
  "_rnenum (_rnmaplets c\<^sub>1 c\<^sub>2 r)" <= "CONST rninsert c\<^sub>1 c\<^sub>2 (_rnenum r)"

  "_rncollect (_evt_param c\<^sub>1 v\<^sub>1) (_evt_param c\<^sub>2 v\<^sub>2) x A P" == "CONST rncollect c\<^sub>1 c\<^sub>2 A (\<lambda> x. ((v\<^sub>1, v\<^sub>2), P))"
  "_rncollect (_evt_id c\<^sub>1) (_evt_param c\<^sub>2 v\<^sub>2) x A P" == "CONST rncollect c\<^sub>1 c\<^sub>2 A (\<lambda> x. (((), v\<^sub>2), P))"
  "_rncollect (_evt_param c\<^sub>1 v\<^sub>1) (_evt_id c\<^sub>2) x A P" == "CONST rncollect c\<^sub>1 c\<^sub>2 A (\<lambda> x. ((v\<^sub>1, ()), P))"
  "_rncollect (_evt_id c\<^sub>1) (_evt_id c\<^sub>2) x A P" == "CONST rncollect c\<^sub>1 c\<^sub>2 A (\<lambda> x. (((), ()), P))"
  "_rncollect_ns e\<^sub>1 e\<^sub>2 x P" == "_rncollect e\<^sub>1 e\<^sub>2 x (CONST UNIV) P"

end
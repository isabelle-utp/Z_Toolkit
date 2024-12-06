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

definition chinst1 :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'a \<Rightarrow> (unit \<Longrightarrow>\<^sub>\<triangle> 'e)" where
"chinst1 c a = \<lparr> prism_match = (\<lambda> e. case match\<^bsub>c\<^esub> e of 
                                       None \<Rightarrow> None 
                                     | Some a' \<Rightarrow> if (a = a') then Some () else None) 
               , prism_build = (\<lambda> b. build\<^bsub>c\<^esub> a) \<rparr>"

lemma chinst1_wb_prism [simp]: "wb_prism c \<Longrightarrow> wb_prism (chinst1 c a)"
  by (simp add: chinst1_def, unfold_locales, auto simp add: option.case_eq_if)

definition chinstn :: "('a \<times> 'b \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'a \<Rightarrow> ('b \<Longrightarrow>\<^sub>\<triangle> 'e)" where
"chinstn c a = \<lparr> prism_match = (\<lambda> e. case match\<^bsub>c\<^esub> e of 
                                       None \<Rightarrow> None 
                                     | Some (a', b') \<Rightarrow> if (a = a') then Some b' else None) 
               , prism_build = (\<lambda> b. build\<^bsub>c\<^esub> (a, b)) \<rparr>"     

lemma chinstn_wb_prism [simp]: "wb_prism c \<Longrightarrow> wb_prism (chinstn c a)"
  by (simp add: chinstn_def, unfold_locales, auto simp add: option.case_eq_if)

text \<open> Syntax is defined for channel instantiation, which selects either @{const chinstn} if the
   type is a product and @{const chinst1} otherwise \<close>

syntax "_chinst" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>._" [100,101] 100)

translations
  "_chinst c v" <= "CONST chinst1 c v"
  "_chinst c v" <= "CONST chinstn c v"

ML_file \<open>Channel_Events.ML\<close>

parse_translation
  \<open>[(@{syntax_const "_chinst"}, 
    fn ctx => fn ts => 
      case ts of 
        [t1, t2] => Channel_Events.chinst ctx t1 t2 |
        _ => raise Match)]\<close>

text \<open> A channel instantiation may have 1 or 2+ parameters, and this can only be decided based on
  the type of the channel (where it's unitary, or a product). We could make channel instantiation
  an overloaded constant, but this introduces issues so for now we assume that we can only instantiate
  a channel with a product view type. In future, we could get the syntax translation mechanisation
  to resolve this. \<close>

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
  "_chan_inst"     :: "chan \<Rightarrow> logic \<Rightarrow> chan" ("_\<^bold>._" [100,101] 101)
  "_chan"          :: "chan \<Rightarrow> chans" ("_")
  "_chans"         :: "chan \<Rightarrow> chans \<Rightarrow> chans" ("_,/ _")
  "_ch_enum"       :: "chans \<Rightarrow> logic" ("\<lbrace>_\<rbrace>")
  "_ch_collect"    :: "id \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<lbrace>_/\<^bold>._ \<in> _./ _\<rbrace>")
  "_ch_collect_ns" :: "id \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<lbrace>_/\<^bold>._./ _\<rbrace>")

translations
  "_chan_id c" => "c"
  "_chan_inst c x" => "_chinst c x" 
  "_chan c" => "CONST csbasic c"
  "_chans e es" => "CONST csinsert e es"
  "_ch_enum A" => "A"
  "_ch_enum (_chan c)" <= "CONST csbasic c"
  "_chan (_chan_inst c x)" <= "_chan (CONST chinstn c x)"
  "_chan_inst (_chan_inst c x) y" <= "_chan_inst (CONST chinstn c x) y"
  "_ch_enum (_chans c cs)" <= "CONST csinsert c (_ch_enum cs)"
  "_ch_collect e x A P" == "CONST cscollect e A (\<lambda> x. P)"
  "_ch_collect_ns e x P" == "_ch_collect e x (CONST UNIV) P"

subsection \<open> Renaming Relations \<close>

nonterminal rnenum

definition rnsingle :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e\<^sub>1) \<Rightarrow> ('a \<Longrightarrow>\<^sub>\<triangle> 'e\<^sub>2) \<Rightarrow> 'e\<^sub>1 \<leftrightarrow> 'e\<^sub>2" where
"rnsingle c\<^sub>1 c\<^sub>2 = {(build\<^bsub>c\<^sub>1\<^esub> v, build\<^bsub>c\<^sub>2\<^esub> v) | v. True}" 

definition rninsert :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e\<^sub>1) \<Rightarrow> ('a \<Longrightarrow>\<^sub>\<triangle> 'e\<^sub>2) \<Rightarrow> ('e\<^sub>1 \<leftrightarrow> 'e\<^sub>2) \<Rightarrow> 'e\<^sub>1 \<leftrightarrow> 'e\<^sub>2" where
"rninsert c\<^sub>1 c\<^sub>2 rn = rnsingle c\<^sub>1 c\<^sub>2 \<union> rn"  

definition rncollect :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e\<^sub>1) \<Rightarrow> ('b \<Longrightarrow>\<^sub>\<triangle> 'e\<^sub>2) \<Rightarrow> 'c set \<Rightarrow> ('c \<Rightarrow> ('a \<times> 'b) \<times> bool) \<Rightarrow> 'e\<^sub>1 \<leftrightarrow> 'e\<^sub>2" where
"rncollect c\<^sub>1 c\<^sub>2 A f = {(build\<^bsub>c\<^sub>1\<^esub> (fst (fst (f x))), build\<^bsub>c\<^sub>2\<^esub> (snd (fst (f x)))) | x. x \<in> A \<and> snd (f x)}"

syntax
  "_rnsingle"      :: "chan \<Rightarrow> chan \<Rightarrow> rnenum" ("_ \<mapsto> _")
  "_rnmaplets"     :: "chan \<Rightarrow> chan \<Rightarrow> rnenum \<Rightarrow> rnenum" ("_ \<mapsto> _,/ _")
  "_rnenum"        :: "rnenum \<Rightarrow> logic" ("\<lbrace>_\<rbrace>")
  "_rncollect"    :: "evt \<Rightarrow> evt \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<lbrace>_ \<mapsto> _ | _ \<in> _./ _\<rbrace>")
  "_rncollect_ns" :: "evt \<Rightarrow> evt \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<lbrace>_ \<mapsto> _ | _./ _\<rbrace>")

translations
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

term "\<lbrace>c\<^bold>.1\<^bold>.y\<rbrace>"

end
section \<open> Pretty Notation for Z \<close>

theory Z_Toolkit_Pretty
  imports Relation_Toolkit Number_Toolkit
  abbrevs "+>" = "\<Zpfun>" and "+>" = "\<Zpsurj>" and "++>" = "\<Zffun>"
    and ">->" = "\<Zinj>" and ">->" = "\<Zbij>" and ">+>" = "\<Zpinj>" and ">++>" = "\<Zfinj>"
    and "<|" = "\<lhd>" and "<|" = "\<Zdres>" and "<|" = "\<Zndres>" and "<|" = "\<lblot>"
    and "|>" = "\<rhd>" and "|>" = "\<Zrres>" and "|>" = "\<Znrres>" and "|>" = "\<rblot>"
    and "|`" = "\<restriction>" and "|`" = "\<upharpoonleft>" and "|`" = "\<Zproject>"
    and "O+" = "\<oplus>"
    and ";;" = "\<Zcomp>" and ";;" = "\<Zsemi>"
    and "PP" = "\<bbbP>" and "FF" = "\<bbbF>"
begin

declare [[coercion_enabled]]

text \<open> Code generation set up \<close>

code_datatype pfun_of_alist

text \<open> Allow partial functions to be written with braces \<close>

syntax
  "_Pfun"     :: "maplets => ('a, 'b) pfun"            ("(1{_})")

bundle Z_Syntax
begin

unbundle Z_Type_Syntax

subsection \<open> Functions \<close>

no_notation funcset (infixr "\<rightarrow>" 60)

notation rel_tfun (infixr "\<rightarrow>" 60)
notation rel_pfun (infixr "\<Zpfun>" 60)
notation rel_ffun (infixr "\<Zffun>" 60)

notation relcomp (infixr "\<Zcomp>" 75)

notation dom_res (infixr "\<Zdres>" 66)
notation ndres (infixr "\<Zndres>" 66)

notation ran_res (infixr "\<Zrres>" 65)
notation nrres (infixr "\<Znrres>" 65)

end



context
  includes Z_Syntax
begin

subsection \<open> Examples \<close>

typ "\<bbbP> \<nat> \<rightarrow> \<nat>"
typ "\<bbbP> \<nat> \<Zpfun> \<bool>"
term "{}"
term "P \<Zcomp> Q"
term "A \<Zdres> B \<Zndres> (P :: \<bbbP>(\<nat>) \<Zpfun> \<bool>)"

term "\<bbbP> \<nat> \<rightarrow> \<nat>"
term "\<nat> \<Zffun> \<nat>"

end

end
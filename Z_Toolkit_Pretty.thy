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

bundle Z_Syntax
begin
  
no_notation funcset (infixr "\<rightarrow>" 60)

subsection \<open> Types \<close>

type_notation set ("\<bbbP> _" [999] 999)

type_notation tfun (infixr "\<rightarrow>" 0)
type_notation pfun (infixr "\<Zpfun>" 0)
type_notation ffun (infixr "\<Zffun>" 0)

notation rel_tfun (infixr "\<rightarrow>" 60)
notation rel_pfun (infixr "\<Zpfun>" 60)
notation rel_ffun (infixr "\<Zffun>" 60)

subsection \<open> Functions \<close>

notation Pow ("\<bbbP>")
notation Fpow ("\<bbbF>")

notation relcomp (infixr "\<Zcomp>" 75)

notation dom_res (infixr "\<Zdres>" 65)
notation ndres (infixr "\<Zndres>" 65)

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
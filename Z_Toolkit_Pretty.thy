section \<open> Pretty Notation for Z \<close>

theory Z_Toolkit_Pretty
  imports Z_Toolkit "HOL-Library.Function_Algebras"
  abbrevs "+>" = "\<Zpfun>"
    and "#>" = "\<Zffun>"
begin

bundle Z_syntax
begin

no_notation funcset (infixr "\<rightarrow>" 60)

subsection \<open> Types \<close>

type_notation set ("\<Zpower> _" [999] 999)
type_notation fset ("\<Zfinset> _" [999] 999)

type_notation tfun (infixr "\<rightarrow>" 0)
type_notation pfun (infixr "\<Zpfun>" 0)
type_notation ffun (infixr "\<Zffun>" 0)

notation rel_tfun (infixr "\<rightarrow>" 60)
notation rel_pfun (infixr "\<Zpfun>" 60)
notation rel_ffun (infixr "\<Zffun>" 60)

subsection \<open> Functions \<close>

notation Pow ("\<Zpower>")
notation Fpow ("\<Zfinset>")

notation relcomp (infixr "\<Zsemi>" 75)

notation dom_res (infixr "\<Zdres>" 65)
notation ndres (infixr "\<Zndres>" 65)

notation ran_res (infixr "\<Zrres>" 65)
notation nrres (infixr "\<Znrres>" 65)

end

context
  includes Z_syntax
begin

subsection \<open> Examples \<close>

typ "\<Zpower>(\<nat>) \<rightarrow> \<nat>"
typ "\<Zpower>(\<nat>) \<Zpfun> \<bool>"

term "P \<Zsemi> Q"
term "A \<Zdres> B \<Zndres> (P :: \<Zfinset>(\<nat>) \<Zpfun> \<bool>)"

term "\<Zpower>(\<nat>) \<rightarrow> \<nat>"
term "\<nat> \<Zffun> \<nat>"

end

end
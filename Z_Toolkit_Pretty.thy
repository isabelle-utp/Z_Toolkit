section \<open> Pretty Notation for Z \<close>

theory Z_Toolkit_Pretty
  imports Z_Toolkit
begin

subsection \<open> Types \<close>

type_notation set ("\<power> _" [999] 999)
type_notation fset ("\<finset> _" [999] 999)
type_notation pfun (infixr "\<Zpfun>" 0)
type_notation ffun (infixr "\<Zffun>" 0)
type_notation tfun (infixr "\<Zfun>" 0)

subsection \<open> Functions \<close>

notation Pow ("\<power>")
notation Fpow ("\<finset>")

notation relcomp (infixr "\<semi>" 75)

notation dom_res (infixr "\<Zdres>" 65)
notation ndres (infixr "\<Zndres>" 65)

notation ran_res (infixr "\<Zrres>" 65)
notation nrres (infixr "\<Znrres>" 65)

subsection \<open> Examples \<close>

typ "\<power>(\<nat>) \<Zfun> \<nat>"
typ "\<finset>(\<nat>) \<Zpfun> \<bool>"

term "P \<semi> Q"
term "A \<Zdres> B \<Zdres> (P :: \<finset>(\<nat>) \<Zpfun> \<bool>)"

end
section \<open> Pretty Notation for Z \<close>

theory Z_Toolkit_Pretty
  imports Z_Toolkit
begin

subsection \<open> Types \<close>

type_notation set ("\<power>'(_')")
type_notation fset ("\<finset>'(_')")
type_notation pfun (infixr "\<pfun>" 0)
type_notation ffun (infixr "\<ffun>" 0)
type_notation tfun (infixr "\<fun>" 0)

subsection \<open> Functions \<close>

notation Pow ("\<power>")
notation Fpow ("\<finset>")

notation relcomp (infixr "\<semi>" 75)

notation dom_res (infixr "\<dres>" 65)
notation ndres (infixr "\<ndres>" 65)

notation ran_res (infixr "\<rres>" 65)
notation ndres (infixr "\<nrres>" 65)

subsection \<open> Examples \<close>

typ "\<power>(\<nat>) \<fun> \<nat>"
typ "\<finset>(\<nat>) \<pfun> \<bool>"

term "P \<semi> Q"
term "A \<dres> B \<dres> (P :: \<finset>(\<nat>) \<pfun> \<bool>)"

end
section \<open> Defining Declared Constants \<close>

theory Def_Const
  imports Main
  keywords "def_const" :: "thy_defn"
begin

text \<open> Add a simple command to define previously declared polymorphic constants. This is 
  particularly useful for handling given sets in Z. \<close>

ML \<open>
let fun def_const n t thy = 
  let val Const (pn, typ) = Proof_Context.read_const {proper = false, strict = false} (Named_Target.theory_init thy) n
      val ctx = Overloading.overloading [(n, (pn, dummyT), false)] thy
      val pt = Syntax.check_term ctx (Type.constraint typ (Syntax.parse_term ctx t))
  in (Local_Theory.exit_global o snd o Local_Theory.define (((Binding.name n), NoSyn), ((Binding.name (n ^ "_def"), [Attrib.check_src @{context} (Token.make_src ("code_unfold", Position.none) [])]), pt))) ctx 
  end in

Outer_Syntax.command @{command_keyword def_const} "define a declared constant"
    ((Parse.name -- Parse.term) >> (fn (n, t) => Toplevel.theory (def_const n t)))
  end
\<close>

end
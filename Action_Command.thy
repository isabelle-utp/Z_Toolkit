section \<open> Define Circus-style Actions \<close>

theory Action_Command
  imports "HOL-Library.Product_Order"
  keywords "actions" :: "thy_defn"
begin

named_theorems action_defs

ML \<open> 
structure Action_Def =
struct

fun act_eq ctx actT t =
  let open Syntax; open HOLogic
      val eq = case parse_term ctx t of 
                 Const ("HOL.eq", _) $ x $ y => check_term ctx (Const ("HOL.eq", actT --> actT --> dummyT) $ x $ y) |
                 _ => raise Match
  in 
    case eq of
      Const ("HOL.eq", _) $ (Free (n, _) $ ps) $ action => 
        ((n, fastype_of ps --> actT), tupled_lambda ps action) |
      Const  ("HOL.eq", _) $ (Free (n, _)) $ action => 
        ((n, actT), action) |
      _ => raise Match
end

fun define_action t actT ctx = 
  let open Syntax; open Logic; open HOLogic
      val lfp = const @{const_name lfp}
      val ((n, typ), actlam) = act_eq ctx actT t
      val actfix = check_term ctx (lfp $ absfree (n, typ) actlam)
      val acteq = mk_equals (Free (n, typ), actfix)
  in
    snd (Specification.definition (SOME (Binding.name n, NONE, NoSyn)) [] [] ((Binding.name (n ^ "_def"), @{attributes [action_defs]}), acteq) ctx) 
  end;

fun tuple_proj n i t =
  let open HOLogic; open Syntax in 
    if n = 1 then t
    else if n = 2 then (if i = 0 then const @{const_name fst} $ t else const @{const_name snd} $ t)
    else (if i = 0 then const @{const_name fst} $ t else tuple_proj (n - 1) (i - 1) (const @{const_name snd} $ t)) 
  end;

fun define_actions ((actsn, raw_actT), ts) ctx = 
  let open Syntax; open HOLogic; open Logic; open Specification;
      val lfp = const @{const_name lfp}
      val actT = read_typ ctx raw_actT
      val eqs = map (act_eq ctx actT) ts
      val acts = mk_tuple (map snd eqs)
      val ps = mk_tuple (map (Free o fst) eqs)
      val actfix = check_term ctx (lfp $ tupled_lambda ps acts)
      val acteq = mk_equals (Free (actsn, dummyT), actfix)
      fun def ctx (n, eq) = definition (SOME (Binding.name n, NONE, NoSyn)) [] [] ((Binding.name (n ^ "_def"), @{attributes [action_defs]}), eq) ctx 
      val ((sys, _), ctx0) = def ctx (actsn, acteq)
      val actnms = map (fn (n, i) => (n, mk_equals (Free (n, dummyT), tuple_proj (length eqs) i sys))) (ListPair.zip (map (fst o fst) eqs, 0 upto (length eqs - 1)))
      val ctx1 = fold (fn eq => fn ctx' => snd (def ctx' eq)) actnms ctx0   
  in
    ctx1
  end;
end;
Outer_Syntax.command 
  @{command_keyword actions}
  "define a system of recursive actions" 
  (((Scan.optional Parse.name "actionsys") -- (@{keyword "is"} |-- Parse.typ)) 
   -- (@{keyword "where"} |-- Parse.enum1 "|" Parse.term) 
   >> (Toplevel.local_theory NONE NONE o Action_Def.define_actions)) 

\<close>

end
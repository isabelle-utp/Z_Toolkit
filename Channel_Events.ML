structure Channel_Events =
struct

(* Deconstruct the view from a prism *)
fun 
  dest_prism_viewT (Type (@{type_name prism_ext}, [a, _, _])) = a |
  dest_prism_viewT t = @{print} t 

(* Remove syntactic constraint annotations from a syntactic term *) 
fun 
  strip_term_constraints (Const ("_constrain", _) $ e $ _) = strip_term_constraints e |
  strip_term_constraints (e $ f) = strip_term_constraints e $ strip_term_constraints f |
  strip_term_constraints (Abs (n, t, trm)) = Abs (n, t, strip_term_constraints trm) |
  strip_term_constraints e = e

(* Given a potentially partially instantiated channel expression and return the view type *) 
fun 
  get_prism_expr_type ctx (Const (@{const_name chinstn}, _) $ c $ _) 
    = snd (HOLogic.dest_prodT (get_prism_expr_type ctx c)) |
  get_prism_expr_type ctx (Const (@{const_name chinst1}, _) $ c $ _) 
    = snd (HOLogic.dest_prodT (get_prism_expr_type ctx c)) |
  get_prism_expr_type ctx (Free (n, t)) = 
   let open Syntax
        val consts = (Proof_Context.consts_of ctx)
        val {const_space, ...} = Consts.dest consts
        \<comment> \<open> The name must be internalised in case it needs qualifying. \<close>
        val c = Consts.intern consts n
        \<comment> \<open> If the name refers to a declared constant, then we lift it as a constant. \<close>
        val trm = check_term ctx (if (Name_Space.declared const_space c) 
                                  then Const (c, t) else Free (n, t)) 
        val ty = (case trm of
                    Free (_, t') => t' | Const (_, t') => t' | _ => t)
   in dest_prism_viewT ty end |
  get_prism_expr_type ctx e = type_of (Syntax.check_term ctx e)


fun
  chinst ctx (Const ("_constrain", _) $ e $ _) v = (chinst ctx e v) |
  chinst ctx (Free (n, t)) v =
    let open Syntax
        val consts = (Proof_Context.consts_of ctx)
        val {const_space, ...} = Consts.dest consts
        \<comment> \<open> The name must be internalised in case it needs qualifying. \<close>
        val c = Consts.intern consts n
        \<comment> \<open> If the name refers to a declared constant, then we lift it as a constant. \<close>
        val trm = check_term ctx (if (Name_Space.declared const_space c) 
                                  then Const (c, t) else Free (n, t)) 
        val ty = (case trm of
                    Free (_, t') => t' | Const (_, t') => t' | _ => t)
    in case ty of 
         Type (@{type_name prism_ext}, [Type (@{type_name "prod"}, [_, _]), _, _]) 
           => Syntax.const @{const_name chinstn} $ Free (n, t) $ v |
         Type (@{type_name prism_ext}, _) 
           => Syntax.const @{const_name chinst1} $ Free (n, t) $ v |
         _ => Syntax.const @{const_name chinstn} $ Free (n, t) $ v
    end |
  chinst ctx e v = 
    let open Syntax; open Term
        val ty = get_prism_expr_type ctx (strip_term_constraints e)
    in case ty of 
         Type (@{type_name "prod"}, [_, _]) 
           => Syntax.const @{const_name chinstn} $ e $ v |
         _ => Syntax.const @{const_name chinst1} $ e $ v
    end
end

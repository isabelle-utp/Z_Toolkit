section \<open> Meta-theory for Relation Library \<close>

theory Relation_Lib
  imports
    Countable_Set_Extra Positive Infinity Enum_Type Record_Default_Instance Def_Const
    Relation_Extra Partial_Fun Partial_Inj Finite_Fun Finite_Inj Total_Fun List_Extra
begin 

text \<open> This theory marks the boundary between reusable library utilities and the creation of the
  Z notation. We avoid overriding any HOL syntax up until this point. \<close>

end
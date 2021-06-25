section \<open> Meta-theory for Relation Library \<close>

theory Relation_Lib
  imports
    Countable_Set_Extra Positive Infinity FSet_Extra 
    Relation_Extra Partial_Fun Partial_Inj Finite_Fun Total_Fun List_Extra
begin 

text \<open> This theory marks the boundary between reusable library utilities and the creation of the
  Z notation. We avoid overriding any HOL syntax up until this point. \<close>

end
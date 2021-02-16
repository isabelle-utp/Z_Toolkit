theory Z_Toolkit
  imports 
    Relation_Toolkit
begin

text \<open> One issue that emerges in this encoding is the treatment of total functions. In Z, a total
  function is a particular kind of partial function whose domain covers the type universe. In HOL,
  a total function is one of the basic types. Typically, one wishes to apply total functions, 
  partial functions, and finite functions to values using the notation @{term "f x"}. In order
  to implement this, we need to coerce the given function @{term f} to a total function, since
  this is fundamental to HOL's application construct. However, that means that we can't also
  coerce a total function to a partial function, as expected by Z, since this would lead to
  a cycle. Consequently, we actually need to create a new ``total function'' type, different
  to the HOL one, to break the cycle.  \<close>

declare [[coercion pfun_of_tfun]]




end
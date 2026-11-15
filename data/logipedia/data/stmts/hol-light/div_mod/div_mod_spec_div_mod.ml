(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.div_mod_spec_div_mod, catalog title
  "div_mod.div_mod_spec_div_mod": for every natural dividend and positive
  natural divisor, the natural quotient and remainder satisfy the division
  specification: the remainder is below the divisor and the dividend is the
  quotient times the divisor plus the remainder. This file contains no proof.
*)

let statement =
  `!n m:num.
     0 < m
     ==>
     n MOD m < m /\
     n = (n DIV m) * m + n MOD m`;;

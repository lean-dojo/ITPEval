(*
  Statement-only formalization of Logipedia corpus artifact bigops.timesA,
  catalog title "bigops.timesA": the source polymorphic Aop predicate holds
  at the natural number one. This file contains no proof.
*)

new_constant
  ("logipedia_bigops_Aop", `:'a -> bool`);;

let statement =
  `logipedia_bigops_Aop (1:num)`;;

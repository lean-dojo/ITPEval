(*
  Statement-only formalization of Logipedia corpus artifact bigops.timesAC,
  catalog title "bigops.timesAC": the source polymorphic ACop predicate holds
  at the natural number one. This file contains no proof.
*)

new_constant
  ("logipedia_bigops_ACop", `:'a -> bool`);;

let statement =
  `logipedia_bigops_ACop (1:num)`;;

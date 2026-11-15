(*
  Statement-only formalization of miniF2F valid problem algebra_apb4leq8ta4pb4. This file
  contains no proof.
*)

let statement =
  `!a b:real.
     &0 < a /\ &0 < b
     ==> (a + b) pow 4 <= &8 * (a pow 4 + b pow 4)`;;

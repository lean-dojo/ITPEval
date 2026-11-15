(*
  Statement-only formalization of miniF2F test problem algebra_9onxpypzleqsum2onxpy. This file
  contains no proof.
*)

let algebra_9onxpypzleqsum2onxpy =
  `!x:real y:real z:real.
     (&0 < x /\ &0 < y /\ &0 < z) ==>
     &9 / (x + y + z) <=
     &2 / (x + y) + &2 / (y + z) + &2 / (z + x)`;;

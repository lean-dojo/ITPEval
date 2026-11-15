(*
  Statement-only formalization of miniF2F test problem amc12a_2009_p6. This file contains no
  proof.
*)

let statement =
  `!m n p q:real.
     p = exp (m * ln (&2)) /\ q = exp (n * ln (&3))
     ==> exp ((&2 * n) * ln p) * exp (m * ln q) =
         exp ((m * n) * ln (&12))`;;

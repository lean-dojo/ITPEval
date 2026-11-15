(*
  Statement-only formalization of miniF2F test problem algebra_bleqa_apbon2msqrtableqambsqon8b.
  This file contains no proof.
*)

let statement =
  `!a b:real.
     (&0 < a /\ &0 < b) /\ b <= a
     ==> (a + b) / &2 - sqrt (a * b)
         <= (a - b) pow 2 / (&8 * b)`;;

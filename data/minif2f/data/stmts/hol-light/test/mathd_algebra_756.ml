(*
  Statement-only formalization of miniF2F test problem mathd_algebra_756:
  real exponentiation identities determining b^a from 2^a and a^b. This file
  contains no proof.
*)

let statement =
  `!a b:real.
     exp (a * ln (&2)) = &32 ==>
     exp (b * ln a) = &125 ==>
     exp (a * ln b) = &243`;;

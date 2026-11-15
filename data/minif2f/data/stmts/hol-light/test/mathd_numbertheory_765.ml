(*
  Statement-only formalization of miniF2F test problem
  mathd_numbertheory_765. The source uses Euclidean integer modulo, so the
  residue equation is stated as the equivalent integer congruence rather than
  HOL Light's sign-sensitive `rem`. This file contains no proof.
*)

let statement =
  `!x:int.
     x < &0 /\
     (&24 * x == &15) (mod &1199)
     ==> x <= -- &449`;;

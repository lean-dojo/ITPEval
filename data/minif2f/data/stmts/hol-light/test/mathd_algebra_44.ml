(*
  Statement-only formalization of miniF2F test problem mathd_algebra_44. This file contains no
  proof.
*)

let statement =
  `!s t:real.
     s = &9 - &2 * t /\
     t = &3 * s + &1
     ==> s = &1 /\ t = &4`;;

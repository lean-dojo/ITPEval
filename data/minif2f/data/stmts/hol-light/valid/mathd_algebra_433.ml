(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_433. This file contains no
  proof.
*)

(*
  miniF2F valid artifact mathd_algebra_433: a real function defined by
  f(x) = 3 * sqrt(2*x - 7) - 8 satisfies f(8) = 1. This is a statement-only
  formalization and contains no proof.
*)

let statement =
  `!f:real->real.
     (!x:real. f x = &3 * sqrt (&2 * x - &7) - &8)
     ==> f (&8) = &1`;;

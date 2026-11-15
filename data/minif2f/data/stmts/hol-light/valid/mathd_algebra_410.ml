(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_410. This file contains no
  proof.
*)

(*
  miniF2F valid artifact mathd_algebra_410: if real numbers x and y satisfy
  y = x^2 - 6*x + 13, then y is at least 4. This is a statement-only
  formalization and contains no proof.
*)

let statement =
  `!x y:real.
     y = x pow 2 - &6 * x + &13
     ==> &4 <= y`;;

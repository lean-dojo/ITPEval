(*
  Statement-only formalization of miniF2F test artifact mathd_algebra_359:
  a real number satisfying y + 6 + y = 2 * 12 must equal 9. This file
  contains no proof.
*)

let mathd_algebra_359 =
  `!y:real. (y + &6) + y = &2 * &12 ==> y = &9`;;

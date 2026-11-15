(*
  Statement-only formalization of miniF2F valid artifact mathd_algebra_536:
  three factorial times the sum of two cubed and the square root of nine,
  divided by two, equals 33. This file contains no proof.
*)

let statement =
  `&(FACT 3) * (&2 pow 3 + sqrt (&9)) / &2 = &33`;;

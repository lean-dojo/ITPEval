(*
  Statement-only formalization of miniF2F valid artifact mathd_algebra_568:
  for every real a, the given polynomial expression equals a^3 + a^2. This
  file contains no proof.
*)

let statement =
  `!a:real.
     (a - &1) * (a + &1) * (a + &2) - (a - &2) * (a + &1) =
     a pow 3 + a pow 2`;;

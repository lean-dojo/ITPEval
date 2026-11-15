(*
  Statement-only formalization of miniF2F test artifact amc12a_2009_p7: a real-valued
  sequence with constant consecutive differences and specified terms reaches 2009 only
  at index 502. This file contains no proof.
*)

let statement =
  `!x:real n:num a:num->real.
     ((!m:num. a (m + 1) - a m = a (m + 2) - a (m + 1)) /\
      a 1 = &2 * x - &3 /\
      a 2 = &5 * x - &11 /\
      a 3 = &3 * x + &1 /\
      a n = &2009)
     ==> n = 502`;;

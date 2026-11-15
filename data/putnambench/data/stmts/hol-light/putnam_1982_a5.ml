(*
  Statement-only formalization of PutnamBench artifact putnam_1982_a5:
  a lower bound for the positive gap below one of a sum of two rational
  numbers with bounded positive numerators. This file contains no proof.
*)

let statement =
  `!a b c d:num.
     0 < a /\
     0 < b /\
     0 < c /\
     0 < d /\
     a + c <= 1982 /\
     &a / &b + &c / &d < &1
     ==> &1 - &a / &b - &c / &d > &1 / (&1983 pow 3)`;;

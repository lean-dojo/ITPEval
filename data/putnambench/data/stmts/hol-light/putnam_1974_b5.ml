(*
  Statement-only formalization of PutnamBench artifact putnam_1974_b5:
  the strict lower bound by half the real exponential for the truncated
  exponential series through its natural-number argument. This file contains
  no proof.
*)

needs "Library/transc.ml";;

let statement =
  `!n:num.
     sum (0..n) (\i. (&n) pow i / &(FACT i)) > exp (&n) / &2`;;

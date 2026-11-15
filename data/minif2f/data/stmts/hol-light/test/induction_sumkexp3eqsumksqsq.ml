(*
  Statement-only formalization of miniF2F test problem
  induction_sumkexp3eqsumksqsq: the sum of cubes is the square of
  the corresponding sum. This file contains no proof.
*)

let statement =
  `!n:num.
     nsum (0..(n - 1)) (\k. k EXP 3) =
     (nsum (0..(n - 1)) (\k. k)) EXP 2`;;

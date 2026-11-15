(*
  Statement-only formalization of miniF2F test problem induction_sumkexp3eqsumksq. This file
  contains no proof.
*)

let induction_sumkexp3eqsumksq =
  `!n:num.
     nsum {k | k < n} (\k. k EXP 3) =
     (nsum {k | k < n} (\k. k)) EXP 2`;;

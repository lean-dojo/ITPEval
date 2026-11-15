(*
  Statement-only formalization of miniF2F test problem amc12_2000_p1:
  three pairwise distinct natural factors of 2001 have bounded sum.
  This file contains no proof.
*)

let statement =
  `!i m n:num.
     ~(i = m) /\ ~(m = n) /\ ~(n = i) /\ i * m * n = 2001
     ==> i + m + n <= 671`;;

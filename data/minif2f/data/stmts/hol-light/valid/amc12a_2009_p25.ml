(*
  Statement-only formalization of miniF2F valid problem amc12a_2009_p25, concerning a
  natural-indexed real sequence governed by a nonlinear recurrence. This file contains no proof.
*)

let statement =
  `!a:num->real.
     (a 1 = &1 /\
      a 2 = &1 / sqrt (&3) /\
      (!n:num. 1 <= n ==>
               a (n + 2) =
               (a n + a (n + 1)) / (&1 - a n * a (n + 1))))
     ==> abs (a 2009) = &0`;;

(*
  Statement-only formalization of miniF2F test problem imo_1974_p3: the
  odd-indexed binomial sum from 0 through n is not divisible by 5. This file
  contains no proof.
*)

needs "Library/binomial.ml";;

let statement =
  `!n:num.
     ~(5 divides
       nsum (0..n)
         (\k. binom (2 * n + 1,2 * k + 1) * 2 EXP (3 * k)))`;;

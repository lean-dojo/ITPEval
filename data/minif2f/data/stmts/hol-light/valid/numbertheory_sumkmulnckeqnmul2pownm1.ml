(*
  Statement-only formalization of miniF2F valid artifact
  numbertheory_sumkmulnckeqnmul2pownm1: for each positive natural n, the sum
  from k = 1 through n of k times the binomial coefficient n choose k equals
  n times 2 raised to n - 1. This file contains no proof.
*)

needs "Library/binomial.ml";;

let statement =
  `!n:num.
     0 < n
     ==> nsum (1..n) (\k. k * binom (n,k)) =
         n * (2 EXP (n - 1))`;;

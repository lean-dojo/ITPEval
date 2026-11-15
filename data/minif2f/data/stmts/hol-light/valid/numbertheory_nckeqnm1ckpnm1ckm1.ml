(*
  Statement-only formalization of miniF2F valid artifact
  numbertheory_nckeqnm1ckpnm1ckm1: Pascal's recurrence for natural-number
  binomial coefficients when n and k are positive and k <= n. This file
  contains no proof.
*)

needs "Library/binomial.ml";;

let statement =
  `!n k:num.
     0 < n /\ 0 < k /\ k <= n
     ==> binom (n,k) = binom (n - 1,k) + binom (n - 1,k - 1)`;;

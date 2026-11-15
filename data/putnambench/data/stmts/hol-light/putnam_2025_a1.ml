(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_a1
  (putnambench__hol-light__putnam_2025_a1): eventual coprimality of the odd
  transforms of two positive integer sequences defined by a rational
  recurrence. This file contains no proof.
*)

let statement =
  `!m n:num->num.
     (!k:num. 0 < m k) /\
     (!k:num. 0 < n k) /\
     ~(m 0 = n 0) /\
     (!k:num. 0 < k ==> coprime(m k,n k)) /\
     (!k:num.
        m (k + 1) * (2 * n k + 1) =
        n (k + 1) * (2 * m k + 1))
     ==> FINITE
           {k:num |
              ~coprime(2 * m k + 1,2 * n k + 1)}`;;

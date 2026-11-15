(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2008_b6:
  the number of k-limited permutations of n points is odd exactly for residues
  0 and 1 modulo 2k+1. This file contains no proof.
*)

let statement =
  `!n k:num.
     0 < n /\ 0 < k
     ==>
     (ODD
        (CARD
          {s:num->num |
             BIJ s {i:num | i < n} {i:num | i < n} /\
             (!i:num. n <= i ==> s i = i) /\
             (!i:num.
                i < n
                ==> s i <= i + k /\ i <= s i + k)})
      <=>
      n MOD (2 * k + 1) = 0 \/ n MOD (2 * k + 1) = 1)`;;

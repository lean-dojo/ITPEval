(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2005_b6:
  the signed sum over permutations of {1,...,n}, weighted by the reciprocal
  of one more than each permutation's number of fixed points. This file
  contains no proof.
*)

let statement =
  `!n:num.
     1 <= n
     ==>
     let permutation_sign =
       \p:num->num.
         if EVEN
              (CARD
                {ij:num#num |
                   FST ij IN (1..n) /\
                   SND ij IN (1..n) /\
                   FST ij < SND ij /\
                   p (SND ij) < p (FST ij)})
         then &1
         else -- &1 in
     sum
       {p:num->num |
          (!x:num. ~(x IN (1..n)) ==> p x = x) /\
          (!y:num. ?!x:num. p x = y)}
       (\p:num->num.
          permutation_sign p /
          (&(CARD {i:num | i IN (1..n) /\ p i = i}) + &1)) =
     ((-- &1) pow (n + 1) * &n) / (&n + &1)`;;

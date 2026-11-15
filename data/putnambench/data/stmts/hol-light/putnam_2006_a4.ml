(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2006_a4:
  the average number of local maxima among the values of a permutation of
  {1,...,n} is (n+1)/3 for every integer n greater than one. This file
  contains no proof.
*)

let statement =
  `let permutations =
     \n:num.
       {p:num->num |
          BIJ p (0..n-1) (0..n-1) /\
          (!i:num. ~(i IN (0..n-1)) ==> p i = i)} in
   let local_maxima =
     \n:num. \p:num->num.
       {k:num |
          k IN (0..n-1) /\
          (k = 0 \/ p (k-1) < p k) /\
          (k = n-1 \/ p k > p (k+1))} in
   !n:num.
     1 < n
     ==>
     sum (permutations n)
         (\p:num->num. &(CARD (local_maxima n p))) /
     &(CARD (permutations n)) =
     (&n + &1) / &3`;;

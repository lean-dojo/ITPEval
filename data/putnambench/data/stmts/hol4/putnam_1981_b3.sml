(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1981_b3:
  infinitely many natural numbers have the property that every prime divisor
  of n^2 + 3 also divides k^2 + 3 for some natural k with k^2 < n. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val putnam_1981_b3 =
  ``!P : num -> bool.
      (!n : num.
         (P n <=>
          !p : num.
            prime p /\ divides p (n EXP 2 + 3)
            ==>
            ?k : num.
              divides p (k EXP 2 + 3) /\ k EXP 2 < n))
      ==>
      !n : num. ?m : num. n < m /\ P m``;

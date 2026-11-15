(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_a5:
  for an odd positive integer q, the number of positive integers below q/4
  and coprime to q is odd exactly when q is a positive power of a prime
  congruent to 5 or 7 modulo 8. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory pred_setTheory primeTheory realTheory;

val putnam_2015_a5 =
  ``!q Nq : num.
      ODD q /\
      0 < q /\
      Nq =
        CARD
          {a : num |
             0 < a /\
             (&a : real) < (&q : real) / 4 /\
             gcd a q = 1}
      ==>
      (ODD Nq <=>
       ?p k : num.
         q = p EXP k /\
         0 < k /\
         prime p /\
         (p MOD 8 = 5 \/ p MOD 8 = 7))``;

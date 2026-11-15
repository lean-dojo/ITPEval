(*
  Statement-only formalization of PutnamBench artifact putnam_1974_a1:
  the maximum size, namely 11, of a subset of the integers from 1 through 16
  containing no three distinct pairwise relatively prime elements. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory integerTheory pred_setTheory;

val putnam_1974_a1 =
  ``let conspiratorial =
      \S : int set.
        !a b c : int.
          a IN S /\ b IN S /\ c IN S
          ==>
          0 < a /\ 0 < b /\ 0 < c /\
          ((a <> b /\ b <> c /\ a <> c)
           ==>
           1 < gcd (Num (ABS a)) (Num (ABS b)) \/
           1 < gcd (Num (ABS b)) (Num (ABS c)) \/
           1 < gcd (Num (ABS a)) (Num (ABS c)))
    in
      (?S : int set.
         FINITE S /\
         S SUBSET {x : int | 1 <= x /\ x <= 16} /\
         conspiratorial S /\
         CARD S = 11) /\
      (!S : int set.
         FINITE S /\
         S SUBSET {x : int | 1 <= x /\ x <= 16} /\
         conspiratorial S
         ==>
         CARD S <= 11)``;

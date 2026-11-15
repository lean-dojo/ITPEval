(*
  Statement-only formalization of PutnamBench artifact putnam_1976_a3:
  the natural prime-power equation |p^r - q^s| = 1, with both exponents
  greater than one, has exactly the two specified ordered solutions. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory;

val putnam_1976_a3 =
  ``!p r q s : num.
      (prime p /\ prime q /\ 1 < r /\ 1 < s /\
       ABS (int_of_num (p ** r) - int_of_num (q ** s)) = 1
       <=>
       (p = 3 /\ r = 2 /\ q = 2 /\ s = 3) \/
       (p = 2 /\ r = 3 /\ q = 3 /\ s = 2))``;

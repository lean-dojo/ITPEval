(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_a4:
  the primes greater than 5 whose powers admit a rearrangement with a fixed
  positive consecutive difference modulo the prime are exactly the prime 7.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory primeTheory;

val putnam_2024_a4 =
  ``{p : num |
       prime p /\
       5 < p /\
       ?a r : int.
         1 <= r /\
         r <= int_of_num p - 1 /\
         ?e : num -> num.
           BIJ e
             {n : num | n <= p - 5}
             {n : num | n <= p - 5} /\
           !n : num.
             1 <= n /\ n <= p - 5
             ==>
             (int_of_num p) int_divides
               (a ** (e n) - a ** (e (n - 1)) - r)} =
    {7}``;

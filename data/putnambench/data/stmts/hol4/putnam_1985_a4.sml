(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1985_a4:
  the last two digits occurring infinitely often in the iterated-power
  sequence a 1 = 3, a (i + 1) = 3^(a i), form the singleton {87}.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_1985_a4 =
  ``!a : num -> num.
      a 1 = 3 /\
      (!i : num. 1 <= i ==> a (i + 1) = 3 EXP (a i))
      ==>
      {k : num |
         k < 100 /\
         !N : num. ?i : num. N <= i /\ a i MOD 100 = k} =
      {87}``;

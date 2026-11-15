(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2007_a5:
  in a finite group, the number of elements of a specified prime order is
  either zero or one less than a multiple of that prime. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory primeTheory monoidTheory
     groupTheory;

val putnam_2007_a5 =
  ``!(g : 'a group) (p n : num).
      FiniteGroup g /\
      prime p /\
      n = CARD (orders g p)
      ==>
      n = 0 \/ p divides (n + 1)``;

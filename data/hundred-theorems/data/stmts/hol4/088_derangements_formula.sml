(*
  Statement-only formalization of Hundred Theorems artifact
  hundred-theorems__hol4__088, cataloged as "Derangements Formula": for every
  nonempty finite set, the number of fixed-point-free permutations is the
  nearest integer to n! / e. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory permutesTheory realTheory transcTheory;

val derangements_formula =
  ``!n (s : 'a set).
      s HAS_SIZE n /\ n <> 0
      ==>
      let derangements =
        {p : 'a -> 'a |
           p permutes s /\ (!x. x IN s ==> p x <> x)}
      in
        FINITE derangements /\
        abs (&(CARD derangements) - &(FACT n) / exp 1) < 1 / 2``;

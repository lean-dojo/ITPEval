(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1134776, "Dilworth's theorem": in a finite partially ordered set, the
  minimum size of a partition into chains equals the maximum size of an
  antichain. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val dilworth_is_chain_def = new_definition (
  "dilworth_is_chain_def",
  ``dilworth_is_chain (le : 'a -> 'a -> bool) (s : 'a set) <=>
      !x y. x IN s /\ y IN s ==> le x y \/ le y x``);

val dilworth_is_antichain_def = new_definition (
  "dilworth_is_antichain_def",
  ``dilworth_is_antichain (le : 'a -> 'a -> bool) (s : 'a set) <=>
      !x y. x IN s /\ y IN s /\ x <> y ==> ~le x y``);

val dilworth_is_chain_partition_def = new_definition (
  "dilworth_is_chain_partition_def",
  ``dilworth_is_chain_partition
      (le : 'a -> 'a -> bool) (C : ('a set) set) <=>
      (!x. ?!s. s IN C /\ x IN s) /\
      (!s. s IN C ==> dilworth_is_chain le s)``);

val dilworth_is_min_chain_partition_size_def = new_definition (
  "dilworth_is_min_chain_partition_size_def",
  ``dilworth_is_min_chain_partition_size
      (le : 'a -> 'a -> bool) (n : num) <=>
      (?C : ('a set) set.
         FINITE C /\
         dilworth_is_chain_partition le C /\
         CARD C = n) /\
      (!C : ('a set) set.
         FINITE C /\ dilworth_is_chain_partition le C
         ==>
         n <= CARD C)``);

val dilworth_is_max_antichain_size_def = new_definition (
  "dilworth_is_max_antichain_size_def",
  ``dilworth_is_max_antichain_size
      (le : 'a -> 'a -> bool) (n : num) <=>
      (?A : 'a set.
         FINITE A /\
         dilworth_is_antichain le A /\
         CARD A = n) /\
      (!A : 'a set.
         FINITE A /\ dilworth_is_antichain le A
         ==>
         CARD A <= n)``);

val minChainPartition_eq_antichainWidth =
  ``!le : 'a -> 'a -> bool.
      FINITE (UNIV : 'a set) /\
      (!x. le x x) /\
      (!x y. le x y /\ le y x ==> x = y) /\
      (!x y z. le x y /\ le y z ==> le x z)
      ==>
      ?n : num.
        dilworth_is_min_chain_partition_size le n /\
        dilworth_is_max_antichain_size le n``;

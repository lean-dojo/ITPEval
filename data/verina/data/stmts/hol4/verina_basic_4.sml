(*
  Statement-only formalization of VERINA artifact verina_basic_4,
  cataloged as "kthElement": the executable program returns the kth integer
  in a nonempty array using valid 1-based indexing. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val kthElement_precond_def = new_definition (
  "kthElement_precond_def",
  ``kthElement_precond (arr : int list) (k : num) <=>
      1 <= k /\ k <= LENGTH arr``
);

val kthElement_def = new_definition (
  "kthElement_def",
  ``kthElement (arr : int list) (k : num) =
      EL (k - 1) arr``
);

val kthElement_postcond_def = new_definition (
  "kthElement_postcond_def",
  ``kthElement_postcond
      (arr : int list) (k : num) (result : int) <=>
      EXISTS
        (\x : int. x = result /\ x = EL (k - 1) arr)
        arr``
);

val kthElement_spec_satisfied =
  ``!(arr : int list) (k : num).
      kthElement_precond arr k ==>
      kthElement_postcond arr k (kthElement arr k)``;

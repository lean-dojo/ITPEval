(*
  Statement-only formalization of VERINA corpus artifact verina_basic_9,
  catalog title "hasCommonElement": the executable Boolean program checks
  whether two nonempty integer arrays share an element, together with its
  bounded-index correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val hasCommonElement_precond_def = new_definition (
  "hasCommonElement_precond_def",
  ``hasCommonElement_precond (a : int list) (b : int list) <=>
      0 < LENGTH a /\ 0 < LENGTH b``
);

val hasCommonElement_def = new_definition (
  "hasCommonElement_def",
  ``hasCommonElement (a : int list) (b : int list) =
      EXISTS
        (\x : int. EXISTS (\y : int. x = y) b)
        a``
);

val hasCommonElement_postcond_def = new_definition (
  "hasCommonElement_postcond_def",
  ``hasCommonElement_postcond
      (a : int list) (b : int list) (result : bool) <=>
      ((?i j : num.
          i < LENGTH a /\
          j < LENGTH b /\
          EL i a = EL j b) <=>
       result)``
);

val hasCommonElement_spec_satisfied =
  ``!(a : int list) (b : int list).
      hasCommonElement_precond a b ==>
      hasCommonElement_postcond a b (hasCommonElement a b)``;

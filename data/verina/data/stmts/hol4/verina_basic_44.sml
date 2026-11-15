(*
  Statement-only formalization of VERINA corpus artifact verina_basic_44,
  catalog title "isOddAtIndexOdd": the executable indexed scan of an integer
  array returns true exactly when every odd index contains an odd integer and
  satisfies that Boolean correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val isOdd_def = new_definition (
  "isOdd_def",
  ``isOdd (n : int) <=> n % 2 = 1``
);

val isOddAtIndexOdd_precond_def = new_definition (
  "isOddAtIndexOdd_precond_def",
  ``isOddAtIndexOdd_precond (a : int list) <=> T``
);

val isOddAtIndexOdd_allFrom_def = Define `
  (isOddAtIndexOdd_allFrom
      (index : num) ([] : int list) = T) /\
  (isOddAtIndexOdd_allFrom
      index (x::xs) =
     ((~isOdd (int_of_num index) \/ isOdd x) /\
      isOddAtIndexOdd_allFrom (SUC index) xs))
`;

val isOddAtIndexOdd_def = new_definition (
  "isOddAtIndexOdd_def",
  ``isOddAtIndexOdd (a : int list) =
      isOddAtIndexOdd_allFrom 0 a``
);

val isOddAtIndexOdd_postcond_def = new_definition (
  "isOddAtIndexOdd_postcond_def",
  ``isOddAtIndexOdd_postcond
      (a : int list) (result : bool) <=>
      (result <=>
       !i : num.
         i < LENGTH a ==>
         isOdd (int_of_num i) ==>
         isOdd (EL i a))``
);

val isOddAtIndexOdd_spec_satisfied =
  ``!a : int list.
      isOddAtIndexOdd_precond a ==>
      isOddAtIndexOdd_postcond a (isOddAtIndexOdd a)``;

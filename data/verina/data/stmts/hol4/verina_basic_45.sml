(*
  Statement-only formalization of VERINA corpus artifact verina_basic_45,
  catalog title "findProduct": the executable integer-list program multiplies
  the entries at the first even and first odd indices under the stated
  length-and-existence precondition and satisfies its match-based correctness
  contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory optionTheory pairTheory;

val isEven_def = new_definition (
  "isEven_def",
  ``isEven (n : int) <=> n % 2 = 0``
);

val isOdd_def = new_definition (
  "isOdd_def",
  ``isOdd (n : int) <=> n % 2 <> 0``
);

val findProduct_findIdx_def = Define `
  (findProduct_findIdx
      (p : int -> bool) ([] : int list) =
     (NONE : num option)) /\
  (findProduct_findIdx
      p (x::xs) =
     if p x then
       SOME 0
     else
       case findProduct_findIdx p xs of
         NONE => NONE
       | SOME index => SOME (SUC index))
`;

val firstEvenOddIndices_def = new_definition (
  "firstEvenOddIndices_def",
  ``firstEvenOddIndices (lst : int list) =
      case findProduct_findIdx isEven lst of
        NONE => (NONE : (num # num) option)
      | SOME evenIndex =>
          case findProduct_findIdx isOdd lst of
            NONE => NONE
          | SOME oddIndex => SOME (evenIndex, oddIndex)``
);

val findProduct_precond_def = new_definition (
  "findProduct_precond_def",
  ``findProduct_precond (lst : int list) <=>
      LENGTH lst > 1 /\
      EXISTS (\x : int. isEven x) lst /\
      EXISTS (\x : int. isOdd x) lst``
);

val findProduct_nthD_def = Define `
  (findProduct_nthD
      (index : num) ([] : int list) = (0 : int)) /\
  (findProduct_nthD
      0 (x::xs) = x) /\
  (findProduct_nthD
      (SUC index) (x::xs) =
     findProduct_nthD index xs)
`;

val findProduct_def = new_definition (
  "findProduct_def",
  ``findProduct (lst : int list) =
      case firstEvenOddIndices lst of
        NONE => (0 : int)
      | SOME indices =>
          findProduct_nthD (FST indices) lst *
          findProduct_nthD (SND indices) lst``
);

val findProduct_postcond_def = new_definition (
  "findProduct_postcond_def",
  ``findProduct_postcond
      (lst : int list) (result : int) <=>
      case firstEvenOddIndices lst of
        NONE => T
      | SOME indices =>
          result =
            findProduct_nthD (FST indices) lst *
            findProduct_nthD (SND indices) lst``
);

val findProduct_spec_satisfied =
  ``!lst : int list.
      findProduct_precond lst ==>
      findProduct_postcond lst (findProduct lst)``;

(*
  Statement-only formalization of VERINA corpus artifact verina_basic_49,
  catalog title "findFirstOdd": the executable left-to-right scan of a
  nonempty integer array returns the natural-number index of its first odd
  entry, or NONE when no odd entry exists, under its complete correctness
  contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory optionTheory;

val isOdd_def = new_definition (
  "isOdd_def",
  ``isOdd (x : int) <=> x % 2 <> 0``
);

val findFirstOdd_precond_def = new_definition (
  "findFirstOdd_precond_def",
  ``findFirstOdd_precond (a : int list) <=>
      LENGTH a > 0``
);

val findFirstOdd_from_def = Define `
  (findFirstOdd_from
      ([] : int list) (index : num) =
     (NONE : num option)) /\
  (findFirstOdd_from
      (x::xs) index =
     if isOdd x then
       SOME index
     else
       findFirstOdd_from xs (SUC index))
`;

val findFirstOdd_def = new_definition (
  "findFirstOdd_def",
  ``findFirstOdd (a : int list) =
      findFirstOdd_from a 0``
);

val findFirstOdd_postcond_def = new_definition (
  "findFirstOdd_postcond_def",
  ``findFirstOdd_postcond
      (a : int list) (result : num option) <=>
      case result of
        SOME index =>
          index < LENGTH a /\
          isOdd (EL index a) /\
          (!j : num.
             j < index ==>
             ~isOdd (EL j a))
      | NONE =>
          !i : num.
            i < LENGTH a ==>
            ~isOdd (EL i a)``
);

val findFirstOdd_spec_satisfied =
  ``!a : int list.
      findFirstOdd_precond a ==>
      findFirstOdd_postcond a (findFirstOdd a)``;

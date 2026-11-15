(*
  Statement-only formalization of VERINA corpus artifact verina_basic_60,
  catalog title "FindEvenNumbers": the executable integer-array program
  scans from left to right and returns exactly the even entries in their
  original order, under its full correctness contract. This file contains
  no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory rich_listTheory;

val isEven_def = new_definition (
  "isEven_def",
  ``isEven (n : int) <=> n % 2 = 0``
);

val FindEvenNumbers_precond_def = new_definition (
  "FindEvenNumbers_precond_def",
  ``FindEvenNumbers_precond (arr : int list) <=> T``
);

val FindEvenNumbers_loop_def = Define `
  (FindEvenNumbers_loop
      ([] : int list) (acc : int list) =
     acc) /\
  (FindEvenNumbers_loop
      (x::xs) acc =
     if isEven x then
       FindEvenNumbers_loop xs (acc ++ [x])
     else
       FindEvenNumbers_loop xs acc)
`;

val FindEvenNumbers_def = new_definition (
  "FindEvenNumbers_def",
  ``FindEvenNumbers (arr : int list) =
      FindEvenNumbers_loop arr []``
);

val FindEvenNumbers_postcond_def = new_definition (
  "FindEvenNumbers_postcond_def",
  ``FindEvenNumbers_postcond
      (arr : int list) (result : int list) <=>
      EVERY isEven result /\
      sublist result arr /\
      LENGTH result = LENGTH (FILTER isEven arr)``
);

val FindEvenNumbers_spec_satisfied =
  ``!arr : int list.
      FindEvenNumbers_precond arr ==>
      FindEvenNumbers_postcond
        arr (FindEvenNumbers arr)``;

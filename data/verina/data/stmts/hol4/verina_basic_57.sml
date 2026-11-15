(*
  Statement-only formalization of VERINA corpus artifact verina_basic_57,
  catalog title "CountLessThan": an executable indexed scan counts the
  integers in an array that are strictly less than a threshold and states its
  total precondition and fold-based correctness contract. This file contains
  no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val CountLessThan_precond_def = new_definition (
  "CountLessThan_precond_def",
  ``CountLessThan_precond
      (numbers : int list) (threshold : int) <=>
      T``
);

val countLessThan_getBang_def = new_definition (
  "countLessThan_getBang_def",
  ``countLessThan_getBang
      (numbers : int list) (i : num) =
      if i < LENGTH numbers then EL i numbers else (0 : int)``
);

val countLessThan_loopFuel_def = Define `
  (countLessThan_loopFuel
      0
      (numbers : int list) (threshold : int)
      (i : num) (acc : num) =
     acc) /\
  (countLessThan_loopFuel
      (SUC fuel) numbers threshold i acc =
     if i < LENGTH numbers then
       let new_acc =
         if countLessThan_getBang numbers i < threshold then
           acc + 1
         else
           acc
       in
         countLessThan_loopFuel
           fuel numbers threshold (i + 1) new_acc
     else
       acc)
`;

val countLessThan_def = new_definition (
  "countLessThan_def",
  ``countLessThan
      (numbers : int list) (threshold : int) =
      countLessThan_loopFuel
        (SUC (LENGTH numbers))
        numbers threshold 0 0``
);

val CountLessThan_def = new_definition (
  "CountLessThan_def",
  ``CountLessThan
      (numbers : int list) (threshold : int) =
      countLessThan numbers threshold``
);

val CountLessThan_postcond_def = new_definition (
  "CountLessThan_postcond_def",
  ``CountLessThan_postcond
      (numbers : int list) (threshold : int) (result : num) <=>
      result -
        FOLDL
          (\count n.
             if n < threshold then count + 1 else count)
          0
          numbers = 0 /\
      FOLDL
        (\count n.
           if n < threshold then count + 1 else count)
        0
        numbers - result = 0``
);

val CountLessThan_spec_satisfied =
  ``!(numbers : int list) (threshold : int).
      CountLessThan_precond numbers threshold ==>
      CountLessThan_postcond
        numbers threshold
        (CountLessThan numbers threshold)``;

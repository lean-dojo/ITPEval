(*
  Statement-only formalization of VERINA corpus artifact verina_basic_81,
  catalog title "DivisionFunction": the executable natural-number division
  program returns an integer remainder-quotient pair, using (x, 0) when the
  divisor is zero, and satisfies the stated division contract. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory pairTheory;

val DivisionFunction_precond_def = new_definition (
  "DivisionFunction_precond_def",
  ``DivisionFunction_precond (x : num) (y : num) <=> T``
);

val divMod_def = new_definition (
  "divMod_def",
  ``divMod (x : num) (y : num) =
      (int_of_num (x MOD y), int_of_num (x DIV y))``
);

val DivisionFunction_def = new_definition (
  "DivisionFunction_def",
  ``DivisionFunction (x : num) (y : num) =
      if y = 0 then
        (int_of_num x, (0 : int))
      else
        divMod x y``
);

val DivisionFunction_postcond_def = new_definition (
  "DivisionFunction_postcond_def",
  ``DivisionFunction_postcond
      (x : num) (y : num) (result : int # int) <=>
      (y = 0 ==>
       FST result = int_of_num x /\
       SND result = (0 : int)) /\
      (y <> 0 ==>
       SND result * int_of_num y + FST result = int_of_num x /\
       (0 <= FST result /\ FST result < int_of_num y) /\
       0 <= SND result)``
);

val DivisionFunction_spec_satisfied =
  ``!(x : num) (y : num).
      DivisionFunction_precond x y ==>
      DivisionFunction_postcond
        x y (DivisionFunction x y)``;

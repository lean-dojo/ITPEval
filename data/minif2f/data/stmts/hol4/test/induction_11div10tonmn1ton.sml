(*
  Statement-only formalization of miniF2F test problem induction_11div10tonmn1ton: divisibility
  by 11 of the integer 10^n - (-1)^n for every natural number n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val induction_11div10tonmn1ton =
  ``!n : num.
      (11 : int) int_divides
        ((10 : int) ** n - (~1 : int) ** n)``;

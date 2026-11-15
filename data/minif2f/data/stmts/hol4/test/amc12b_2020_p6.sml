(*
  Statement-only formalization of miniF2F test problem amc12b_2020_p6: for every natural
  n at least 9, the quotient of a difference of consecutive factorials by n factorial is
  the square of a natural number. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val _ = new_theory "hello";

val amc12b_2020_p6 =
  ``!n : num.
      9 <= n ==>
      ?x : num.
        (&(x EXP 2) : real) =
        (&(FACT (n + 2)) - &(FACT (n + 1))) / &(FACT n)``;

val _ = export_theory();

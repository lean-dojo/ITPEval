(*
  Statement-only formalization of "Euler's Generalization of Fermat's Little Theorem" from
  Hundred Theorems item 010. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory numberTheory;

val eulers_generalization_of_fermats_little_theorem =
  ``!a : num.
      !n : num.
        coprime a n ==>
        (a EXP (totient n)) MOD n = (1 MOD n)``;

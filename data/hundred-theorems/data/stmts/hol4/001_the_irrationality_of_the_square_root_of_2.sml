(*
  Statement-only formalization of "The Irrationality of the Square Root of 2" from Hundred
  Theorems item 001. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory transcTheory;

val irrational_sqrt_two =
  ``~(?p q : num.
      ~(q = 0) /\
      abs (sqrt (2 : real)) = &p / &q)``;

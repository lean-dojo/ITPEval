(*
  Statement-only formalization of PutnamBench artifact putnam_1975_b5:
  the infinite sum formed from a recursively differentiated sequence beginning
  with the real exponential function equals exp (exp 1). This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory seqTheory limTheory transcTheory;

val putnam_1975_b5 =
  ``!f : num -> real -> real.
      (!x : real. f 0 x = exp x) /\
      (!n : num. !x : real.
         f (n + 1) x = x * diffn 1 (f n) x)
      ==>
      suminf
        (\n : num. f n 1 / &(FACT n)) =
      exp (exp 1)``;

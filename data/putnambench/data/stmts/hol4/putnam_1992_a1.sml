(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1992_a1:
  the characterization of the integer function f(n) = 1 - n by two functional
  identities and the initial value f(0) = 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val putnam_1992_a1 =
  ``!f : int -> int.
      (f = (\n : int. 1 - n)) <=>
      ((!n : int. f (f n) = n) /\
       (!n : int. f (f (n + 2) + 2) = n) /\
       f 0 = 1)``;

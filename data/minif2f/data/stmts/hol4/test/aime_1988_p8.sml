(*
  Statement-only formalization of miniF2F artifact aime_1988_p8: a real-valued function on
  pairs of naturals satisfying positive-input diagonal, symmetry, and functional-equation
  conditions, with conclusion f(14, 52) = 364. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val _ = new_theory "hello";

val aime_1988_p8 =
  ``!f : num -> num -> real.
      (!x. 0 < x ==> f x x = &x) /\
      (!x y. 0 < x /\ 0 < y ==> f x y = f y x) /\
      (!x y.
         0 < x /\ 0 < y ==>
         (&x + &y) * f x y = &y * f x (x + y))
      ==>
      f 14 52 = 364``;

val _ = export_theory();

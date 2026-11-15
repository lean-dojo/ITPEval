(*
  Statement-only formalization of PutnamBench artifact putnam_1969_a6:
  convergence of a real sequence y_n = x_(n-1) + 2*x_n for n >= 2 implies
  convergence of the real sequence x_n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory real_topologyTheory;

val putnam_1969_a6 =
  ``!x y : num -> real.
      (!n : num.
         2 <= n
         ==>
         y n = x (n - 1) + 2 * x n) /\
      (?c : real. (y --> c) sequentially)
      ==>
      ?C : real. (x --> C) sequentially``;

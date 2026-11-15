(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1987_b4:
  the two real sequences defined by the given trigonometric recurrence
  converge respectively to negative one and zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory real_topologyTheory transcTheory;

val putnam_1987_b4 =
  ``!x y : num -> real.
      x 1 = 4 / 5 /\
      y 1 = 3 / 5 /\
      (!n : num.
         1 <= n
         ==>
         x (n + 1) =
           x n * cos (y n) - y n * sin (y n)) /\
      (!n : num.
         1 <= n
         ==>
         y (n + 1) =
           x n * sin (y n) + y n * cos (y n))
      ==>
      (x --> (~1 : real)) sequentially /\
      (y --> 0) sequentially``;

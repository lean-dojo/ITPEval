(*
  Statement-only formalization of PutnamBench artifact putnam_1972_a3:
  real functions preserving Cesaro convergence for every sequence in [0,1]
  are exactly the functions affine on [0,1]. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory;

val putnam_1972_a3 =
  ``let climit_exists =
      \x : num -> real.
        ?C : real.
          ((\n : num. SIGMA x (count n) / &n) --> C) sequentially
    in
    let supercontinuous =
      \f : real -> real.
        !x : num -> real.
          ((!i : num. 0 <= x i /\ x i <= 1) /\
           climit_exists x)
          ==>
          climit_exists (\i : num. f (x i))
    in
      !f : real -> real.
        supercontinuous f
        <=>
        ?A B : real.
          !x : real.
            0 <= x /\ x <= 1
            ==>
            f x = A * x + B``;

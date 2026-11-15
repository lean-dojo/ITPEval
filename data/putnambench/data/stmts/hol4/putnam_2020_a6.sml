(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2020_a6:
  the least uniform upper bound of the specified finite sine sums over all
  positive integer indices and real arguments is pi / 4. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory transcTheory;

val putnam_2020_a6 =
  ``let f =
      \N : num.
      \x : real.
        SIGMA
          (\n : num.
             (&N + 1 / 2 - &n) /
               ((&N + 1) * (2 * &n + 1)) *
             sin ((2 * &n + 1) * x))
          (count (SUC N))
    in
    let solution = (pi / 4 : real)
    in
      (!N : num. 0 < N ==> !x : real. f N x <= solution) /\
      (!M : real.
         (!N : num. 0 < N ==> !x : real. f N x <= M)
         ==>
         solution <= M)``;

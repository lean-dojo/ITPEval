(*
  Statement-only formalization of PutnamBench artifact putnam_1965_b1:
  the limit of squared-cosine integrals over growing-dimensional unit cubes.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory realTheory real_topologyTheory;
open transcTheory integrationTheory;

val putnam_1965_b1 =
  ``let integrate_coordinate =
      \g : real list -> real.
      \xs : real list.
        integration$integral (interval [0, 1])
          (\x : real. g (x::xs))
    in
    let cube_integral =
      \n : num.
        FUNPOW integrate_coordinate (n + 1)
          (\xs : real list.
             cos (pi / (2 * &(n + 1)) * FOLDR $+ 0 xs) pow 2)
          []
    in
      (cube_integral --> (1 / 2 : real)) sequentially``;

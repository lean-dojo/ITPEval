(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1227703, "Dirichlet's approximation theorem": for every positive
  circumference, every point on the additive real circle, and every positive
  n, some multiplier from 1 through n brings the point within
  circumference/(n+1) of zero. A real lift represents the circle point, and
  its quotient norm is expressed as distance to an integer multiple of the
  circumference. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory realTheory intrealTheory;

val addCircle_exists_norm_nsmul_le =
  ``!T x : real. !n : num.
      0 < T /\ 0 < n
      ==>
      ?j : num. ?k : int.
        1 <= j /\
        j <= n /\
        abs (&j * x - real_of_int k * T) <= T / &(n + 1)``;

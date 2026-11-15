(*
  Statement-only formalization of PutnamBench artifact putnam_1977_b5:
  a quadratic bound on a finite real sequence forces A below twice every
  pairwise product. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_1977_b5 =
  ``!n : num. !a : num -> real. !A : real.
      let indices = IMAGE SUC (count n)
      in
        1 < n /\
        A + SIGMA (\i : num. a i pow 2) indices <
          1 / ((&n : real) - 1) * (SIGMA a indices) pow 2
        ==>
        !i j : num.
          i IN indices /\ j IN indices /\ i < j
          ==>
          A < 2 * a i * a j``;

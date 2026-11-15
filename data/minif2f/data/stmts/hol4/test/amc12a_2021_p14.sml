(*
  Statement-only formalization of miniF2F test problem amc12a_2021_p14: the
  product of two finite logarithm-ratio sums equals 21000. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory transcTheory;

val _ = new_theory "hello";

val amc12a_2021_p14 =
  ``SIGMA
      (\k. ln (&(3 EXP (k EXP 2))) / ln (&(5 EXP k)))
      (IMAGE SUC (count 20)) *
    SIGMA
      (\k. ln (&(25 EXP k)) / ln (&(9 EXP k)))
      (IMAGE SUC (count 100)) =
    (21000 : real)``;

val _ = export_theory();

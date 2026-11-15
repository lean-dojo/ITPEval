(*
  Statement-only formalization of miniF2F test problem
  algebra_others_exirrpowirrrat: there exist two irrational real numbers whose
  real power is rational. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_of_ratTheory transcTheory;

val algebra_others_exirrpowirrrat =
  ``?a b : real.
      a NOTIN q_set /\
      b NOTIN q_set /\
      a powr b IN q_set``;

(*
  Statement-only formalization of miniF2F test problem amc12a_2009_p6: an identity for real
  powers of 2, 3, and 12. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val amc12a_2009_p6 =
  ``!m n p q : real.
      p = 2 powr m /\
      q = 3 powr n
      ==>
      p powr (2 * n) * q powr m = 12 powr (m * n)``;

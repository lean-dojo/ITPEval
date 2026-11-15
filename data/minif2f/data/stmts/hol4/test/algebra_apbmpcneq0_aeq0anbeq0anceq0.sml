(*
  Statement-only formalization of miniF2F test problem
  algebra_apbmpcneq0_aeq0anbeq0anceq0: the positive real cube roots of 2 and 4, together with
  1, are linearly independent over the rationals. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory ratTheory real_of_ratTheory;

val algebra_apbmpcneq0_aeq0anbeq0anceq0 =
  ``!a b c : rat. !m n : real.
      0 < m /\ 0 < n /\
      m pow 3 = 2 /\
      n pow 3 = 4 /\
      real_of_rat a + real_of_rat b * m + real_of_rat c * n = 0
      ==>
      a = 0 /\ b = 0 /\ c = 0``;

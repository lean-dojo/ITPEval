(*
  Statement-only formalization of miniF2F valid problem amc12a_2019_p21: a product of finite
  complex power sums for z = (1 + i) / sqrt 2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory complexTheory;

val _ = new_theory "hello";

val amc12a_2019_p21 =
  ``!z : complex.
      z = (1 + i) / complex_of_real (sqrt 2)
      ==>
      ITSET
        (\k acc. z pow (k EXP 2) + acc)
        (IMAGE SUC (count 12))
        0 *
      ITSET
        (\k acc. 1 / z pow (k EXP 2) + acc)
        (IMAGE SUC (count 12))
        0 = 36``;

val _ = export_theory();

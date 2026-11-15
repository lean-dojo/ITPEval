(*
  Statement-only formalization of miniF2F test problem amc12a_2020_p7: an integer-valued
  difference of finite square sums for natural sequence values fixed by cube equations. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val _ = new_theory "hello";

val amc12a_2020_p7 =
  ``!a : num -> num.
      (a 0) ** 3 = 1 /\
      (a 1) ** 3 = 8 /\
      (a 2) ** 3 = 27 /\
      (a 3) ** 3 = 64 /\
      (a 4) ** 3 = 125 /\
      (a 5) ** 3 = 216 /\
      (a 6) ** 3 = 343
      ==>
      int_of_num
        (SIGMA (\k. 6 * (a k) ** 2) (count 7)) -
      int_of_num
        (2 * SIGMA (\k. (a k) ** 2) (count 6)) =
      (658 : int)``;

val _ = export_theory();

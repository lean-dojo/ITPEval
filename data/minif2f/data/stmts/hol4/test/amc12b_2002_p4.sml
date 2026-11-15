(*
  Statement-only formalization of miniF2F test problem amc12b_2002_p4: a positive natural
  number whose reciprocal sum with 1/2, 1/3, and 1/7 is integral must equal 42. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory ratTheory;

val amc12b_2002_p4 =
  ``!n : num.
      0 < n /\
      RATD (1q / 2q + 1q / 3q + 1q / 7q + 1q / rat_of_num n) = 1
      ==>
      n = 42``;

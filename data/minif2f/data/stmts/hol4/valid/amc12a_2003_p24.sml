(*
  Statement-only formalization of miniF2F valid problem amc12a_2003_p24: a logarithmic
  expression on real numbers 1 < b <= a has greatest attainable value 0. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val amc12a_2003_p24 =
  ``(?a b : real.
       1 < b /\
       b <= a /\
       ln (a / b) / ln a + ln (b / a) / ln b = 0) /\
    !a b : real.
      1 < b /\
      b <= a
      ==>
      ln (a / b) / ln a + ln (b / a) / ln b <= 0``;

(*
  Statement-only formalization of miniF2F test problem mathd_algebra_392: an even natural
  number with a prescribed centered sum of squares satisfies a divided-product identity.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory;

val mathd_algebra_392 =
  ``!n : num.
      EVEN n /\
      (int_of_num n - 2) ** 2 +
        int_of_num n ** 2 +
        (int_of_num n + 2) ** 2 =
      (12296 : int)
      ==>
      ((n - 2) * n * (n + 2)) DIV 8 = 32736``;

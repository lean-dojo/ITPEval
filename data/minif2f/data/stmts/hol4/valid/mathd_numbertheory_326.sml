(*
  Statement-only formalization of miniF2F valid problem mathd_numbertheory_326:
  a natural number whose three consecutive integer factors multiply to 720 has
  successor 10. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory;

val mathd_numbertheory_326 =
  ``!n : num.
      (int_of_num n - 1) * int_of_num n * (int_of_num n + 1) = 720
      ==>
      n + 1 = 10``;

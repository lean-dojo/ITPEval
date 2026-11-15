(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_320:
  a natural number below 101 whose difference from 123456 is divisible by 101
  must equal 34. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val mathd_numbertheory_320 =
  ``!n : num.
      n < 101 /\
      divides 101 (123456 - n)
      ==>
      n = 34``;

(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_175: the remainder
  of 2^2010 upon division by 10 is 4. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_175 =
  ``(2 EXP 2010) MOD 10 = 4``;

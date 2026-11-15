(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bignum_BigNum_addqtvc: a verification condition for adding two valid
  base-dependent integer-list big numbers, preserving validity and the sum of
  their represented integer values. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val bignum_value_def = Define `
  (bignum_value base ([] : int list) = 0) /\
  (bignum_value base (d :: r) =
     d + base * bignum_value base r)`;

val bignum_valid_def = Define `
  (bignum_valid base ([] : int list) = T) /\
  (bignum_valid base (d :: r) =
     if r = [] then
       0 < d /\ d < base
     else
       (0 <= d /\ d < base) /\ bignum_valid base r)`;

val bignum_add_vc =
  ``!base : int.
      1 < base ==>
      !n1 n2 : int list.
        bignum_valid base n1 ==>
        bignum_valid base n2 ==>
        bignum_valid base n1 /\
        bignum_valid base n2 /\
        (0 : int) <= 0 /\
        (0 : int) <= 1 /\
        !result : int list.
          bignum_valid base result /\
          bignum_value base result =
            bignum_value base n1 + bignum_value base n2 + (0 : int) ==>
          bignum_valid base result /\
          bignum_value base result =
            bignum_value base n1 + bignum_value base n2``;

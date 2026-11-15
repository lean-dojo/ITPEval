(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bignum_BigNum_add_digitqtvc: a verification condition for adding one
  valid base-dependent digit to an integer-list big number, preserving digit
  validity and the represented integer value. This file contains no proof.
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

val bignum_add_digit_vc =
  ``!base : int.
      1 < base ==>
      !n : int list.
      !d : int.
        bignum_valid base n ==>
        0 <= d ==>
        d < base ==>
        ((case n of
            [] => T
          | d0 :: r =>
              ~(d + d0 < base) ==>
              (case n of
                 [] => F
               | ignored :: f => f = r) /\
              bignum_valid base r /\
              (0 : int) <= 1 /\
              (1 : int) < base) /\
         !result : int list.
           (case n of
              [] =>
                if d = 0 then
                  result = ([] : int list)
                else
                  result = [d]
            | d0 :: r =>
                if d + d0 < base then
                  result = (d + d0) :: r
                else
                  ?o1 : int list.
                    (bignum_valid base o1 /\
                     bignum_value base o1 =
                       bignum_value base r + 1) /\
                    result = (d + d0 - base) :: o1) ==>
           bignum_valid base result /\
           bignum_value base result =
             bignum_value base n + d)``;

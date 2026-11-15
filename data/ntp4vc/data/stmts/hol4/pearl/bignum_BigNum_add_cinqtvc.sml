(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bignum_BigNum_add_cinqtvc: a verification condition for adding two
  base-dependent integer-list big numbers with an input carry, preserving
  digit validity and the represented integer value. This file contains no
  proof.
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

val bignum_add_cin_vc =
  ``!base : int.
      1 < base ==>
      !n1 n2 : int list.
      !cin : int.
        bignum_valid base n1 ==>
        bignum_valid base n2 ==>
        0 <= cin ==>
        cin <= 1 ==>
        ((case n2 of
            [] =>
              (case n1 of
                 [] =>
                   bignum_valid base n2 /\
                   0 <= cin /\
                   cin < base
               | x :: x1 =>
                   bignum_valid base n1 /\
                   0 <= cin /\
                   cin < base)
          | x :: x1 =>
              (case n1 of
                 [] =>
                   bignum_valid base n2 /\
                   0 <= cin /\
                   cin < base
               | x2 :: x3 =>
                   if cin + x2 + x < base then
                     (case n1 of
                        [] => F
                      | ignored :: f => f = x3) /\
                     bignum_valid base x3 /\
                     bignum_valid base x1 /\
                     (0 : int) <= 0 /\
                     (0 : int) <= 1
                   else
                     (case n1 of
                        [] => F
                      | ignored :: f => f = x3) /\
                     bignum_valid base x3 /\
                     bignum_valid base x1 /\
                     (0 : int) <= 1 /\
                     (1 : int) <= 1)) /\
         !result : int list.
           (case n2 of
              [] =>
                (case n1 of
                   [] =>
                     bignum_valid base result /\
                     bignum_value base result =
                       bignum_value base n2 + cin
                 | x :: x1 =>
                     bignum_valid base result /\
                     bignum_value base result =
                       bignum_value base n1 + cin)
            | x :: x1 =>
                (case n1 of
                   [] =>
                     bignum_valid base result /\
                     bignum_value base result =
                       bignum_value base n2 + cin
                 | x2 :: x3 =>
                     let d = cin + x2 + x in
                       if d < base then
                         ?o1 : int list.
                           (bignum_valid base o1 /\
                            bignum_value base o1 =
                              bignum_value base x3 +
                              bignum_value base x1 +
                              (0 : int)) /\
                           result = d :: o1
                       else
                         ?o1 : int list.
                           (bignum_valid base o1 /\
                            bignum_value base o1 =
                              bignum_value base x3 +
                              bignum_value base x1 +
                              (1 : int)) /\
                           result = (d - base) :: o1)) ==>
           bignum_valid base result /\
           bignum_value base result =
             bignum_value base n1 +
             bignum_value base n2 +
             cin)``;

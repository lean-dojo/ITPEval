(*
  Statement-only formalization of PutnamBench artifact putnam_1965_b3:
  exactly three ordered positive integer-sided right triangles have area
  equal to twice their perimeter. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory pred_setTheory realTheory intrealTheory;

val putnam_1965_b3 =
  ``CARD
      {abc : int # int # int |
         let a = FST abc in
         let b = FST (SND abc) in
         let c = SND (SND abc) in
           0 < a /\
           a <= b /\
           0 < c /\
           a ** 2 + b ** 2 = c ** 2 /\
           real_of_int a * real_of_int b / 2 =
             2 * (real_of_int a + real_of_int b + real_of_int c)}
      = 3``;

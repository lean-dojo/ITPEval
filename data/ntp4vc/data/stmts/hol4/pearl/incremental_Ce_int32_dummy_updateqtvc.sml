(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/incremental_Ce_int32_dummy_updateqtvc: a signed 32-bit dummy-update
  verification condition involving assignment of 42 and a subsequent doubled
  value. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory wordsTheory;

val dummy_update_int32_in_bounds_def = Define `
  dummy_update_int32_in_bounds (x : int) <=>
    -(2147483648 : int) <= x /\ x <= (2147483647 : int)`;

val incremental_Ce_int32_dummy_update_vc =
  ``!r : word32.
      w2i r = (22 : int) ==>
      dummy_update_int32_in_bounds (42 : int) /\
      (!o1 : word32.
         w2i o1 = (42 : int) ==>
         dummy_update_int32_in_bounds (w2i o1 + w2i o1) /\
         (!o2 : word32.
            w2i o2 = w2i o1 + w2i o1 ==>
            w2i o2 = (42 : int)))``;

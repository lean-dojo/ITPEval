(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/div_Div_invert_limbqtvc: the verification condition
  that division of the maximal 64-bit limb and its divisor complement by a
  normalized divisor yields the prescribed reciprocal limb. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory wordsTheory;

val invert_limb_radix_def = Define `
  invert_limb_radix = (18446744073709551616 : int)`;

val invert_limb_uint_def = Define `
  invert_limb_uint (x : word64) = &(w2n x)`;

val invert_limb_uint64_in_bounds_def = Define `
  invert_limb_uint64_in_bounds (z : int) <=>
    (0 : int) <= z /\ z <= (18446744073709551615 : int)`;

val invert_limb_uint64_max_def = Define `
  invert_limb_uint64_max = (n2w 18446744073709551615 : word64)`;

val invert_limb_reciprocal_def = Define `
  invert_limb_reciprocal (v : word64) (d : word64) <=>
    invert_limb_uint v =
      (invert_limb_radix * invert_limb_radix - (1 : int)) /
        invert_limb_uint d -
      invert_limb_radix`;

val div_Div_invert_limbqtvc_statement =
  ``!d : word64.
      invert_limb_radix / (2 : int) <= invert_limb_uint d ==>
      let o1 : word64 = invert_limb_uint64_max in
        invert_limb_uint64_in_bounds
          (invert_limb_uint o1 - invert_limb_uint d) /\
        (!o2 : word64.
           invert_limb_uint o2 =
             invert_limb_uint o1 - invert_limb_uint d
           ==>
           invert_limb_uint o2 < invert_limb_uint d /\
           (!v : word64.
              invert_limb_uint v =
                (invert_limb_uint invert_limb_uint64_max +
                 invert_limb_radix * invert_limb_uint o2) /
                  invert_limb_uint d
              ==>
              invert_limb_reciprocal v d))``;

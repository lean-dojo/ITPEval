(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/int_sqrt_Why3_ide_VCint_sqrt_loop_term_decrease_goal1:
  a nonzero unsigned 64-bit integer strictly decreases after a logical right
  shift by two, under the verification condition's integer range hypotheses.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val goal1 =
  ``let vc_is_uint64 =
      \z : int. 0 <= z /\ z < 18446744073709551616
    in
      !vc_lsr : int -> int -> int.
        (!z : int. vc_lsr z 0 = z) ==>
        (!z : int.
          0 <= z ==>
          vc_lsr z 1 = z / 2) ==>
        (!p q z : int.
          0 <= p ==>
          0 <= q ==>
          vc_lsr (vc_lsr z p) q = vc_lsr z (p + q)) ==>
        !i_1 i : int.
          let x = vc_lsr i_1 2 in
            i_1 <> 0 ==>
            2 <= i ==>
            vc_is_uint64 i ==>
            vc_is_uint64 i_1 ==>
            vc_is_uint64 x ==>
            x < i_1``;

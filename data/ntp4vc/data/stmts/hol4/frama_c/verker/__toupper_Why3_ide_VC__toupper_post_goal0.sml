(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/__toupper_Why3_ide_VC__toupper_post_goal0:
  the postcondition of an ASCII toupper operation under byte-conversion,
  lowercase-test, and conditional output assumptions. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val goal0 =
  ``let vc_is_lower =
      \c : int. 97 <= c /\ c <= 122
    in
    let vc_is_uint8 =
      \z : int. 0 <= z /\ z < 256
    in
    let vc_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
      !to_sint8 : int -> int.
      !to_uint8 : int -> int.
      !l_toupper : int -> int.
        (!z : int. vc_is_sint8 (to_sint8 z)) ==>
        (!z : int.
          vc_is_sint8 z ==>
          to_sint8 z = z) ==>
        (!z : int. vc_is_uint8 (to_uint8 z)) ==>
        (!z : int.
          vc_is_uint8 z ==>
          to_uint8 z = z) ==>
        (!z : int.
          to_sint8 (to_uint8 z) = to_sint8 z) ==>
        (!c : int.
          l_toupper c =
            if vc_is_lower c then c - 32 else c) ==>
        !i_1 i i_2 : int.
          (vc_is_lower (to_sint8 i_1) <=> i <> 0) ==>
          vc_is_uint8 i ==>
          vc_is_uint8 i_1 ==>
          vc_is_uint8 i_2 ==>
          (if i = 0 then
             i_2 = i_1
           else
             to_uint8 (i_1 - 32) = i_2) ==>
          l_toupper i_1 = i_2``;

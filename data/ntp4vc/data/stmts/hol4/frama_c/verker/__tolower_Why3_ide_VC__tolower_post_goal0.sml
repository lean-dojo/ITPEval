(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/__tolower_Why3_ide_VC__tolower_post_goal0:
  the postcondition of an ASCII tolower operation under byte-conversion,
  uppercase-test, and conditional output assumptions. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val goal0 =
  ``let vc_is_upper =
      \c : int. 65 <= c /\ c <= 90
    in
    let vc_is_uint8 =
      \z : int. 0 <= z /\ z < 256
    in
    let vc_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
      !to_sint8 : int -> int.
      !to_uint8 : int -> int.
      !l_tolower : int -> int.
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
          l_tolower c =
            if vc_is_upper c then c + 32 else c) ==>
        !i_1 i i_2 : int.
          (vc_is_upper (to_sint8 i_1) <=> i <> 0) ==>
          vc_is_uint8 i ==>
          vc_is_uint8 i_1 ==>
          vc_is_uint8 i_2 ==>
          (if i = 0 then
             i_2 = i_1
           else
             to_uint8 (32 + i_1) = i_2) ==>
          l_tolower i_1 = i_2``;

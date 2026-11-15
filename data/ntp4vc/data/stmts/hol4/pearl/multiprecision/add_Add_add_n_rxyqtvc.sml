(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/add_Add_add_n_rxyqtvc: the verification condition for
  doubling an in-place multiprecision integer, including carry arithmetic,
  memory framing, and preservation of pointer bounds and length. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory listTheory wordsTheory;

Datatype:
  mpaddrxy_ptr =
    MpAddrxyPtr (word64 list) int int int bool 'zone
End

val mpaddrxy_data_def = Define `
  mpaddrxy_data
      (MpAddrxyPtr data offset minimum maximum writable zone) =
    data`;

val mpaddrxy_offset_def = Define `
  mpaddrxy_offset
      (MpAddrxyPtr data offset minimum maximum writable zone) =
    offset`;

val mpaddrxy_minimum_def = Define `
  mpaddrxy_minimum
      (MpAddrxyPtr data offset minimum maximum writable zone) =
    minimum`;

val mpaddrxy_maximum_def = Define `
  mpaddrxy_maximum
      (MpAddrxyPtr data offset minimum maximum writable zone) =
    maximum`;

val mpaddrxy_writable_def = Define `
  mpaddrxy_writable
      (MpAddrxyPtr data offset minimum maximum writable zone) =
    writable`;

val mpaddrxy_zone_def = Define `
  mpaddrxy_zone
      (MpAddrxyPtr data offset minimum maximum writable zone) =
    zone`;

val mpaddrxy_to_num_def = Define `
  mpaddrxy_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val mpaddrxy_pelts_def = Define `
  mpaddrxy_pelts (p : 'zone mpaddrxy_ptr) (index : int) =
    if mpaddrxy_to_num index < LENGTH (mpaddrxy_data p) then
      EL (mpaddrxy_to_num index) (mpaddrxy_data p)
    else
      (0w : word64)`;

val mpaddrxy_plength_def = Define `
  mpaddrxy_plength (p : 'zone mpaddrxy_ptr) =
    &(LENGTH (mpaddrxy_data p))`;

val mpaddrxy_int32_in_bounds_def = Define `
  mpaddrxy_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val mpaddrxy_valid_def = Define `
  mpaddrxy_valid (p : 'zone mpaddrxy_ptr) (size : int) <=>
    mpaddrxy_int32_in_bounds size /\
    (0 : int) <= size /\
    ((0 : int) <= mpaddrxy_minimum p /\
     mpaddrxy_minimum p <= mpaddrxy_offset p) /\
    mpaddrxy_offset p + size <= mpaddrxy_maximum p /\
    mpaddrxy_maximum p <= mpaddrxy_plength p`;

val mpaddrxy_radix_def = Define `
  mpaddrxy_radix = (18446744073709551616 : int)`;

val mpaddrxy_radix_power_def = Define `
  mpaddrxy_radix_power (exponent : int) =
    mpaddrxy_radix ** mpaddrxy_to_num exponent`;

val mpaddrxy_value_from_def = Define `
  (mpaddrxy_value_from
      (p : 'zone mpaddrxy_ptr) (index : int) 0 =
     (0 : int)) /\
  (mpaddrxy_value_from p index (SUC count) =
     &(w2n (mpaddrxy_pelts p index)) +
       mpaddrxy_radix *
         mpaddrxy_value_from p (index + (1 : int)) count)`;

val mpaddrxy_value_def = Define `
  mpaddrxy_value (p : 'zone mpaddrxy_ptr) (size : int) =
    mpaddrxy_value_from
      p (mpaddrxy_offset p) (mpaddrxy_to_num size)`;

val mpaddrxy_same_shape_def = Define `
  mpaddrxy_same_shape
      (current : 'zone mpaddrxy_ptr)
      (original : 'zone mpaddrxy_ptr) <=>
    LENGTH (mpaddrxy_data current) =
      LENGTH (mpaddrxy_data original) /\
    mpaddrxy_offset current = mpaddrxy_offset original /\
    mpaddrxy_minimum current = mpaddrxy_minimum original /\
    mpaddrxy_maximum current = mpaddrxy_maximum original /\
    mpaddrxy_writable current = mpaddrxy_writable original /\
    mpaddrxy_zone current = mpaddrxy_zone original`;

val mpaddrxy_frame_def = Define `
  mpaddrxy_frame
      (current : 'zone mpaddrxy_ptr)
      (original : 'zone mpaddrxy_ptr)
      (size : int) <=>
    !j : int.
      j < mpaddrxy_offset current \/
      mpaddrxy_offset current + size <= j ==>
      mpaddrxy_pelts current j = mpaddrxy_pelts original j`;

val mpaddrxy_core_postcondition_def = Define `
  mpaddrxy_core_postcondition
      (current : 'zone mpaddrxy_ptr)
      (original : 'zone mpaddrxy_ptr)
      (size : int)
      (carry : word64) <=>
    mpaddrxy_value current size +
        mpaddrxy_radix_power size * &(w2n carry) =
      mpaddrxy_value original size +
        mpaddrxy_value original size /\
    ((0 : int) <= &(w2n carry) /\ &(w2n carry) <= (1 : int)) /\
    mpaddrxy_frame current original size`;

val add_Add_add_n_rxy_vc =
  ``!size : word32.
    !original : 'zone mpaddrxy_ptr.
      (0 : int) <= w2i size ==>
      mpaddrxy_writable original = T ==>
      mpaddrxy_valid original (w2i size) ==>
      (0 : int) <= w2i size /\
      mpaddrxy_valid original (w2i size) /\
      mpaddrxy_writable original = T /\
      (!current : 'zone mpaddrxy_ptr.
         mpaddrxy_same_shape current original ==>
         (!carry : word64.
            mpaddrxy_core_postcondition
              current original (w2i size) carry ==>
            mpaddrxy_core_postcondition
              current original (w2i size) carry /\
            mpaddrxy_minimum current =
              mpaddrxy_minimum original /\
            mpaddrxy_maximum current =
              mpaddrxy_maximum original /\
            mpaddrxy_plength current =
              mpaddrxy_plength original))``;

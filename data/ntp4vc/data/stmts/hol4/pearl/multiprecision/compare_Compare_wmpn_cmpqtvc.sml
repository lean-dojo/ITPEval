(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/compare_Compare_wmpn_cmpqtvc: the verification
  condition for comparing two unsigned multiprecision limb arrays, including
  pointer validity, the descending-loop suffix invariant, limb bounds, and
  the radix-2^64 integer interpretation. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory listTheory wordsTheory;

val mpcmp_radix_def = Define `
  mpcmp_radix = (18446744073709551616 : int)`;

val mpcmp_to_num_def = Define `
  mpcmp_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val mpcmp_int32_in_bounds_def = Define `
  mpcmp_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val mpcmp_pelts_def = Define `
  mpcmp_pelts
      (data : 'p -> word64 list) (p : 'p) (index : int) =
    if mpcmp_to_num index < LENGTH (data p) then
      EL (mpcmp_to_num index) (data p)
    else
      (0w : word64)`;

val mpcmp_plength_def = Define `
  mpcmp_plength (data : 'p -> word64 list) (p : 'p) =
    &(LENGTH (data p))`;

val mpcmp_valid_def = Define `
  mpcmp_valid
      (data : 'p -> word64 list)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (size : int) <=>
    mpcmp_int32_in_bounds size /\
    (0 : int) <= size /\
    ((0 : int) <= minimum p /\ minimum p <= offset p) /\
    offset p + size <= maximum p /\
    maximum p <= mpcmp_plength data p`;

val mpcmp_valid_ptr_shift_def = Define `
  mpcmp_valid_ptr_shift
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (index : int) <=>
    minimum p <= offset p + index /\
    offset p + index < maximum p`;

val mpcmp_value_from_def = Define `
  (mpcmp_value_from
      (data : 'p -> word64 list) (p : 'p) (index : int) 0 =
     (0 : int)) /\
  (mpcmp_value_from data p index (SUC count) =
     &(w2n (mpcmp_pelts data p index)) +
       mpcmp_radix *
         mpcmp_value_from data p (index + (1 : int)) count)`;

val mpcmp_value_def = Define `
  mpcmp_value
      (data : 'p -> word64 list)
      (offset : 'p -> int)
      (p : 'p)
      (size : int) =
    mpcmp_value_from
      data p (offset p) (mpcmp_to_num size)`;

val mpcmp_compare_int_def = Define `
  mpcmp_compare_int (x : int) (y : int) =
    if x < y then -(1 : int)
    else if x = y then (0 : int)
    else (1 : int)`;

val mpcmp_suffix_equal_def = Define `
  mpcmp_suffix_equal
      (data : 'p -> word64 list)
      (offset : 'p -> int)
      (x : 'p)
      (y : 'p)
      (lower : int)
      (upper : int) <=>
    !j : int.
      lower <= j /\ j < upper ==>
      mpcmp_pelts data x (offset x + j) =
        mpcmp_pelts data y (offset y + j)`;

val mpcmp_loop_invariant_def = Define `
  mpcmp_loop_invariant
      (data : 'p -> word64 list)
      (offset : 'p -> int)
      (x : 'p)
      (y : 'p)
      (index : word32)
      (size : word32) <=>
    ((0 : int) <= w2i index /\ w2i index <= w2i size) /\
    mpcmp_suffix_equal
      data offset x y (w2i index) (w2i size)`;

val compare_Compare_wmpn_cmpqtvc_statement =
  ``!data : 'p -> word64 list.
    !offset minimum maximum : 'p -> int.
    !x : 'p.
    !sz : word32.
    !y : 'p.
      mpcmp_valid data offset minimum maximum x (w2i sz) ==>
      mpcmp_valid data offset minimum maximum y (w2i sz) ==>
      (0 : int) <= w2i sz /\
      w2i sz <= w2i sz /\
      mpcmp_suffix_equal data offset x y (w2i sz) (w2i sz) /\
      (!i : word32.
         mpcmp_loop_invariant data offset x y i sz ==>
         if (1 : int) <= w2i i then
           mpcmp_int32_in_bounds (w2i i - (1 : int)) /\
           (!o1 : word32.
              w2i o1 = w2i i - (1 : int) ==>
              mpcmp_valid_ptr_shift offset minimum maximum x (w2i o1) /\
              (let lx : word64 =
                 mpcmp_pelts data x (offset x + w2i o1)
               in
                 mpcmp_valid_ptr_shift
                   offset minimum maximum y (w2i o1) /\
                 (let ly : word64 =
                    mpcmp_pelts data y (offset y + w2i o1)
                  in
                    !o2 : bool.
                      (((&(w2n lx) = &(w2n ly)) ==> o2 = T) /\
                       (o2 = T ==> lx = ly)) ==>
                      if ~(o2 = T) then
                        if &(w2n ly) < &(w2n lx) then
                          (1 : int) =
                            mpcmp_compare_int
                              (mpcmp_value data offset x (w2i sz))
                              (mpcmp_value data offset y (w2i sz))
                        else
                          -(1 : int) =
                            mpcmp_compare_int
                              (mpcmp_value data offset x (w2i sz))
                              (mpcmp_value data offset y (w2i sz))
                      else
                        w2i o1 < w2i i /\
                        mpcmp_loop_invariant
                          data offset x y o1 sz)))
         else
           (0 : int) =
             mpcmp_compare_int
               (mpcmp_value data offset x (w2i sz))
               (mpcmp_value data offset y (w2i sz)))``;

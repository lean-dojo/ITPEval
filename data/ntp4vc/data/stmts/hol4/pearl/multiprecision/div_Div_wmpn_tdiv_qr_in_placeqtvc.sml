(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/div_Div_wmpn_tdiv_qr_in_placeqtvc: the allocation and
  call verification condition for in-place multiprecision quotient-and-
  remainder division, including scratch-pointer validity and the quotient-
  remainder value relation. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory listTheory wordsTheory;

val wtq_radix_def = Define `
  wtq_radix = (18446744073709551616 : int)`;

val wtq_to_num_def = Define `
  wtq_to_num (z : int) = if z < (0 : int) then 0 else Num z`;

val wtq_uint32_def = Define `
  wtq_uint32 (w : word32) = &(w2n w)`;

val wtq_uint64_def = Define `
  wtq_uint64 (w : word64) = &(w2n w)`;

val wtq_int32_in_bounds_def = Define `
  wtq_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val wtq_uint32_in_bounds_def = Define `
  wtq_uint32_in_bounds (z : int) <=>
    (0 : int) <= z /\ z <= (4294967295 : int)`;

(* The observation tuple is exactly (data, offset, min, max, writable, zone). *)
val wtq_data_def = Define `
  wtq_data
      (obs :
        'p -> word64 list # (int # (int # (int # (bool # 'z)))))
      (p : 'p) =
    FST (obs p)`;

val wtq_offset_def = Define `
  wtq_offset obs (p : 'p) =
    FST (SND (obs p))`;

val wtq_minimum_def = Define `
  wtq_minimum obs (p : 'p) =
    FST (SND (SND (obs p)))`;

val wtq_maximum_def = Define `
  wtq_maximum obs (p : 'p) =
    FST (SND (SND (SND (obs p))))`;

val wtq_writable_def = Define `
  wtq_writable obs (p : 'p) =
    FST (SND (SND (SND (SND (obs p)))))`;

val wtq_zone_def = Define `
  wtq_zone obs (p : 'p) =
    SND (SND (SND (SND (SND (obs p)))))`;

val wtq_plength_def = Define `
  wtq_plength obs (p : 'p) = &(LENGTH (wtq_data obs p))`;

val wtq_pelts_def = Define `
  wtq_pelts obs (p : 'p) (index : int) =
    if wtq_to_num index < LENGTH (wtq_data obs p) then
      EL (wtq_to_num index) (wtq_data obs p)
    else
      (0w : word64)`;

val wtq_valid_def = Define `
  wtq_valid obs (p : 'p) (size : int) <=>
    wtq_int32_in_bounds size /\
    (0 : int) <= size /\
    ((0 : int) <= wtq_minimum obs p /\
     wtq_minimum obs p <= wtq_offset obs p) /\
    wtq_offset obs p + size <= wtq_maximum obs p /\
    wtq_maximum obs p <= wtq_plength obs p`;

val wtq_same_shape_def = Define `
  wtq_same_shape obs (newer : 'p) (older : 'p) <=>
    LENGTH (wtq_data obs newer) = LENGTH (wtq_data obs older) /\
    wtq_offset obs newer = wtq_offset obs older /\
    wtq_minimum obs newer = wtq_minimum obs older /\
    wtq_maximum obs newer = wtq_maximum obs older /\
    wtq_writable obs newer = wtq_writable obs older /\
    wtq_zone obs newer = wtq_zone obs older`;

val wtq_value_from_def = Define `
  (wtq_value_from obs (p : 'p) (index : int) 0 = (0 : int)) /\
  (wtq_value_from obs p index (SUC count) =
     wtq_uint64 (wtq_pelts obs p index) +
       wtq_radix *
         wtq_value_from obs p (index + (1 : int)) count)`;

val wtq_value_def = Define `
  wtq_value obs (p : 'p) (size : int) =
    wtq_value_from
      obs p (wtq_offset obs p) (wtq_to_num size)`;

val wtq_malloc_shape_def = Define `
  wtq_malloc_shape
      obs (null_zone : 'z) (p : 'p) (size : int) <=>
    (~(wtq_zone obs p = null_zone) ==>
       wtq_plength obs p = size) /\
    wtq_offset obs p = (0 : int) /\
    wtq_minimum obs p = (0 : int) /\
    wtq_maximum obs p = wtq_plength obs p /\
    wtq_writable obs p = T`;

val wtq_is_not_null_spec_def = Define `
  wtq_is_not_null_spec
      obs (null_zone : 'z) (is_not_null : 'p -> bool) (p : 'p) <=>
    is_not_null p = ~(wtq_zone obs p = null_zone)`;

val wtq_freed_shape_def = Define `
  wtq_freed_shape obs (p : 'p) <=>
    wtq_offset obs p = (0 : int) /\
    wtq_minimum obs p = (0 : int) /\
    wtq_maximum obs p = wtq_plength obs p /\
    wtq_writable obs p = T`;

val wtq_division_post_def = Define `
  wtq_division_post
      obs (original_x : 'p) (q : 'p) (y : 'p) (remainder : 'p)
      (sx : word32) (sy : word32) <=>
    wtq_value obs original_x (w2i sx) =
      wtq_value obs q (w2i sx - w2i sy + (1 : int)) *
        wtq_value obs y (w2i sy) +
      wtq_value obs remainder (w2i sy) /\
    wtq_value obs remainder (w2i sy) <
      wtq_value obs y (w2i sy)`;

val wtq_div_qr_in_place_pre_def = Define `
  wtq_div_qr_in_place_pre
      obs (sy : word32) (sx : word32)
      (x : 'p) (y : 'p) (q : 'p) (nx : 'p) (ny : 'p) <=>
    ((1 : int) <= w2i sy /\
     w2i sy <= w2i sx /\
     w2i sx <= (2147483647 : int) - (1 : int)) /\
    wtq_valid obs x (w2i sx) /\
    wtq_valid obs y (w2i sy) /\
    wtq_valid obs q (w2i sx - w2i sy + (1 : int)) /\
    wtq_valid obs nx (w2i sx + (1 : int)) /\
    wtq_valid obs ny (w2i sy) /\
    (wtq_writable obs q = T /\ wtq_writable obs x = T) /\
    (wtq_writable obs nx = T /\ wtq_writable obs ny = T) /\
    (0 : int) <
      wtq_uint64
        (wtq_pelts obs y
          (wtq_offset obs y + w2i sy - (1 : int)))`;

val div_Div_wmpn_tdiv_qr_in_placeqtvc_statement =
  ``!obs :
       'p -> word64 list # (int # (int # (int # (bool # 'z)))).
    !null_zone : 'z.
    !is_not_null : 'p -> bool.
    !sy sx : word32.
    !x y q : 'p.
    !qxn : word32.
      (1 : int) <= w2i sy ==>
      w2i sy <= w2i sx ==>
      w2i sx <= (2147483647 : int) - (1 : int) ==>
      wtq_valid obs x (w2i sx) ==>
      wtq_valid obs y (w2i sy) ==>
      wtq_valid obs q (w2i sx - w2i sy + (1 : int)) ==>
      wtq_writable obs x = T ==>
      wtq_writable obs q = T ==>
      w2i qxn = (0 : int) ==>
      (0 : int) <
        wtq_uint64
          (wtq_pelts obs y
            (wtq_offset obs y + w2i sy - (1 : int))) ==>
      (0 : int) <= w2i sx /\
      (!o1 : word32.
         wtq_uint32 o1 = w2i sx ==>
         wtq_uint32_in_bounds (wtq_uint32 o1 + (1 : int)) /\
         (!o2 : word32.
            wtq_uint32 o2 = wtq_uint32 o1 + (1 : int) ==>
            (0 : int) <= wtq_uint32 o2 /\
            (!nx : 'p.
               wtq_malloc_shape obs null_zone nx (wtq_uint32 o2) ==>
               wtq_is_not_null_spec
                 obs null_zone is_not_null nx ==>
               is_not_null nx ==>
               (0 : int) <= w2i sy /\
               (!o3 : word32.
                  wtq_uint32 o3 = w2i sy ==>
                  (0 : int) <= wtq_uint32 o3 /\
                  (!ny : 'p.
                     wtq_malloc_shape
                       obs null_zone ny (wtq_uint32 o3) ==>
                     wtq_is_not_null_spec
                       obs null_zone is_not_null ny ==>
                     is_not_null ny ==>
                     wtq_div_qr_in_place_pre
                       obs sy sx x y q nx ny /\
                     (!ny1 nx1 x1 q1 : 'p.
                        wtq_same_shape obs ny1 ny ==>
                        wtq_same_shape obs nx1 nx ==>
                        wtq_same_shape obs x1 x ==>
                        wtq_same_shape obs q1 q ==>
                        wtq_division_post
                          obs x q1 y x1 sx sy ==>
                        wtq_freed_shape obs nx1 /\
                        wtq_freed_shape obs ny1 /\
                        wtq_division_post
                          obs x q1 y x1 sx sy)))))))``;

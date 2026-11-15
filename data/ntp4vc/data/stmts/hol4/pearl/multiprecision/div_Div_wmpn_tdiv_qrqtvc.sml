(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/div_Div_wmpn_tdiv_qrqtvc: the allocation and call
  verification condition for multiprecision quotient-and-remainder division,
  including scratch-pointer validity, frame conditions, and the resulting
  quotient-remainder value relation. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory listTheory wordsTheory;

val wtdqr_radix_def = Define `
  wtdqr_radix = (18446744073709551616 : int)`;

val wtdqr_to_num_def = Define `
  wtdqr_to_num (z : int) = if z < (0 : int) then 0 else Num z`;

val wtdqr_uint32_def = Define `
  wtdqr_uint32 (w : word32) = &(w2n w)`;

val wtdqr_uint64_def = Define `
  wtdqr_uint64 (w : word64) = &(w2n w)`;

val wtdqr_int32_in_bounds_def = Define `
  wtdqr_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val wtdqr_uint32_in_bounds_def = Define `
  wtdqr_uint32_in_bounds (z : int) <=>
    (0 : int) <= z /\ z <= (4294967295 : int)`;

(* The observation tuple is exactly (data, offset, min, max, writable, zone). *)
val wtdqr_data_def = Define `
  wtdqr_data
      (obs :
        'p -> word64 list # (int # (int # (int # (bool # 'z)))))
      (p : 'p) =
    FST (obs p)`;

val wtdqr_offset_def = Define `
  wtdqr_offset obs (p : 'p) =
    FST (SND (obs p))`;

val wtdqr_minimum_def = Define `
  wtdqr_minimum obs (p : 'p) =
    FST (SND (SND (obs p)))`;

val wtdqr_maximum_def = Define `
  wtdqr_maximum obs (p : 'p) =
    FST (SND (SND (SND (obs p))))`;

val wtdqr_writable_def = Define `
  wtdqr_writable obs (p : 'p) =
    FST (SND (SND (SND (SND (obs p)))))`;

val wtdqr_zone_def = Define `
  wtdqr_zone obs (p : 'p) =
    SND (SND (SND (SND (SND (obs p)))))`;

val wtdqr_plength_def = Define `
  wtdqr_plength obs (p : 'p) = &(LENGTH (wtdqr_data obs p))`;

val wtdqr_pelts_def = Define `
  wtdqr_pelts obs (p : 'p) (index : int) =
    if wtdqr_to_num index < LENGTH (wtdqr_data obs p) then
      EL (wtdqr_to_num index) (wtdqr_data obs p)
    else
      (0w : word64)`;

val wtdqr_valid_def = Define `
  wtdqr_valid obs (p : 'p) (size : int) <=>
    wtdqr_int32_in_bounds size /\
    (0 : int) <= size /\
    ((0 : int) <= wtdqr_minimum obs p /\
     wtdqr_minimum obs p <= wtdqr_offset obs p) /\
    wtdqr_offset obs p + size <= wtdqr_maximum obs p /\
    wtdqr_maximum obs p <= wtdqr_plength obs p`;

val wtdqr_same_shape_def = Define `
  wtdqr_same_shape obs (newer : 'p) (older : 'p) <=>
    LENGTH (wtdqr_data obs newer) = LENGTH (wtdqr_data obs older) /\
    wtdqr_offset obs newer = wtdqr_offset obs older /\
    wtdqr_minimum obs newer = wtdqr_minimum obs older /\
    wtdqr_maximum obs newer = wtdqr_maximum obs older /\
    wtdqr_writable obs newer = wtdqr_writable obs older /\
    wtdqr_zone obs newer = wtdqr_zone obs older`;

val wtdqr_value_from_def = Define `
  (wtdqr_value_from obs (p : 'p) (index : int) 0 = (0 : int)) /\
  (wtdqr_value_from obs p index (SUC count) =
     wtdqr_uint64 (wtdqr_pelts obs p index) +
       wtdqr_radix *
         wtdqr_value_from obs p (index + (1 : int)) count)`;

val wtdqr_value_def = Define `
  wtdqr_value obs (p : 'p) (size : int) =
    wtdqr_value_from
      obs p (wtdqr_offset obs p) (wtdqr_to_num size)`;

val wtdqr_malloc_shape_def = Define `
  wtdqr_malloc_shape
      obs (null_zone : 'z) (p : 'p) (size : int) <=>
    (~(wtdqr_zone obs p = null_zone) ==>
       wtdqr_plength obs p = size) /\
    wtdqr_offset obs p = (0 : int) /\
    wtdqr_minimum obs p = (0 : int) /\
    wtdqr_maximum obs p = wtdqr_plength obs p /\
    wtdqr_writable obs p = T`;

val wtdqr_is_not_null_spec_def = Define `
  wtdqr_is_not_null_spec
      obs (null_zone : 'z) (is_not_null : 'p -> bool) (p : 'p) <=>
    is_not_null p = ~(wtdqr_zone obs p = null_zone)`;

val wtdqr_freed_shape_def = Define `
  wtdqr_freed_shape obs (p : 'p) <=>
    wtdqr_offset obs p = (0 : int) /\
    wtdqr_minimum obs p = (0 : int) /\
    wtdqr_maximum obs p = wtdqr_plength obs p /\
    wtdqr_writable obs p = T`;

val wtdqr_division_post_def = Define `
  wtdqr_division_post
      obs (original_x : 'p) (q : 'p) (y : 'p) (remainder : 'p)
      (sx : word32) (sy : word32) <=>
    wtdqr_value obs original_x (w2i sx) =
      wtdqr_value obs q (w2i sx - w2i sy + (1 : int)) *
        wtdqr_value obs y (w2i sy) +
      wtdqr_value obs remainder (w2i sy) /\
    wtdqr_value obs remainder (w2i sy) <
      wtdqr_value obs y (w2i sy)`;

val wtdqr_div_qr_pre_def = Define `
  wtdqr_div_qr_pre
      obs (sy : word32) (sx : word32)
      (x : 'p) (y : 'p) (q : 'p) (r : 'p) (nx : 'p) (ny : 'p) <=>
    ((1 : int) <= w2i sy /\
     w2i sy <= w2i sx /\
     w2i sx <= (2147483647 : int) - (1 : int)) /\
    wtdqr_valid obs x (w2i sx) /\
    wtdqr_valid obs y (w2i sy) /\
    wtdqr_valid obs q (w2i sx - w2i sy + (1 : int)) /\
    wtdqr_valid obs r (w2i sy) /\
    wtdqr_valid obs nx (w2i sx + (1 : int)) /\
    wtdqr_valid obs ny (w2i sy) /\
    (wtdqr_writable obs nx = T /\ wtdqr_writable obs ny = T) /\
    (0 : int) <
      wtdqr_uint64
        (wtdqr_pelts obs y
          (wtdqr_offset obs y + w2i sy - (1 : int))) /\
    wtdqr_writable obs q = T /\
    wtdqr_writable obs r = T`;

val div_Div_wmpn_tdiv_qrqtvc_statement =
  ``!obs :
       'p -> word64 list # (int # (int # (int # (bool # 'z)))).
    !null_zone : 'z.
    !is_not_null : 'p -> bool.
    !sy sx : word32.
    !x y q r : 'p.
    !qxn : word32.
      (1 : int) <= w2i sy ==>
      w2i sy <= w2i sx ==>
      w2i sx <= (2147483647 : int) - (1 : int) ==>
      wtdqr_valid obs x (w2i sx) ==>
      wtdqr_valid obs y (w2i sy) ==>
      wtdqr_valid obs q (w2i sx - w2i sy + (1 : int)) ==>
      wtdqr_valid obs r (w2i sy) ==>
      wtdqr_writable obs q = T ==>
      wtdqr_writable obs r = T ==>
      w2i qxn = (0 : int) ==>
      (0 : int) <
        wtdqr_uint64
          (wtdqr_pelts obs y
            (wtdqr_offset obs y + w2i sy - (1 : int))) ==>
      (0 : int) <= w2i sx /\
      (!o1 : word32.
         wtdqr_uint32 o1 = w2i sx ==>
         wtdqr_uint32_in_bounds (wtdqr_uint32 o1 + (1 : int)) /\
         (!o2 : word32.
            wtdqr_uint32 o2 = wtdqr_uint32 o1 + (1 : int) ==>
            (0 : int) <= wtdqr_uint32 o2 /\
            (!nx : 'p.
               wtdqr_malloc_shape obs null_zone nx (wtdqr_uint32 o2) ==>
               wtdqr_is_not_null_spec
                 obs null_zone is_not_null nx ==>
               is_not_null nx ==>
               (0 : int) <= w2i sy /\
               (!o3 : word32.
                  wtdqr_uint32 o3 = w2i sy ==>
                  (0 : int) <= wtdqr_uint32 o3 /\
                  (!ny : 'p.
                     wtdqr_malloc_shape
                       obs null_zone ny (wtdqr_uint32 o3) ==>
                     wtdqr_is_not_null_spec
                       obs null_zone is_not_null ny ==>
                     is_not_null ny ==>
                     wtdqr_div_qr_pre
                       obs sy sx x y q r nx ny /\
                     (!ny1 nx1 r1 q1 : 'p.
                        wtdqr_same_shape obs ny1 ny ==>
                        wtdqr_same_shape obs nx1 nx ==>
                        wtdqr_same_shape obs r1 r ==>
                        wtdqr_same_shape obs q1 q ==>
                        wtdqr_division_post
                          obs x q1 y r1 sx sy ==>
                        wtdqr_freed_shape obs nx1 /\
                        wtdqr_freed_shape obs ny1 /\
                        wtdqr_division_post
                          obs x q1 y r1 sx sy))))))``;

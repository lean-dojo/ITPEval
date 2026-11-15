(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/get_str_Get_str_wmpn_get_str_bitsqtvc: the complete
  verification condition for converting a positive multiprecision limb array
  to base-2^bits digits, including fixed-width conversions, loop invariants,
  pointer updates, value preservation, digit bounds, and memory framing.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory listTheory wordsTheory;

val gstr_radix_def = Define `
  gstr_radix = (18446744073709551616 : int)`;

val gstr_to_num_def = Define `
  gstr_to_num (z : int) = if z < (0 : int) then 0 else Num z`;

val gstr_u64_def = Define `
  gstr_u64 (x : word64) = &(w2n x)`;

val gstr_u32_def = Define `
  gstr_u32 (x : word32) = &(w2n x)`;

val gstr_u8_def = Define `
  gstr_u8 (x : word8) = &(w2n x)`;

val gstr_int32_in_bounds_def = Define `
  gstr_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val gstr_uint64_in_bounds_def = Define `
  gstr_uint64_in_bounds (z : int) <=>
    (0 : int) <= z /\ z <= (18446744073709551615 : int)`;

val gstr_ipow_def = Define `
  gstr_ipow (base : int) (exponent : int) =
    base ** gstr_to_num exponent`;

val gstr_ediv_def = Define `
  gstr_ediv (x : int) (y : int) = x / y`;

val gstr_cdiv_def = Define `
  gstr_cdiv (x : int) (y : int) = x quot y`;

val gstr_cmod_def = Define `
  gstr_cmod (x : int) (y : int) = x rem y`;

(* The observation tuple is exactly (data, offset, min, max, writable, zone). *)
val gstr_data_def = Define `
  gstr_data
      (obs :
        'p -> 'a list # (int # (int # (int # (bool # 'z)))))
      (p : 'p) =
    FST (obs p)`;

val gstr_offset_def = Define `
  gstr_offset obs (p : 'p) =
    FST (SND (obs p))`;

val gstr_minimum_def = Define `
  gstr_minimum obs (p : 'p) =
    FST (SND (SND (obs p)))`;

val gstr_maximum_def = Define `
  gstr_maximum obs (p : 'p) =
    FST (SND (SND (SND (obs p))))`;

val gstr_writable_def = Define `
  gstr_writable obs (p : 'p) =
    FST (SND (SND (SND (SND (obs p)))))`;

val gstr_zone_def = Define `
  gstr_zone obs (p : 'p) =
    SND (SND (SND (SND (SND (obs p)))))`;

val gstr_pelts64_def = Define `
  gstr_pelts64 obs (p : 'p) (index : int) =
    if gstr_to_num index < LENGTH (gstr_data obs p) then
      EL (gstr_to_num index) (gstr_data obs p)
    else
      (0w : word64)`;

val gstr_pelts8_def = Define `
  gstr_pelts8 obs (p : 'p) (index : int) =
    if gstr_to_num index < LENGTH (gstr_data obs p) then
      EL (gstr_to_num index) (gstr_data obs p)
    else
      (0w : word8)`;

val gstr_plength_def = Define `
  gstr_plength obs (p : 'p) = &(LENGTH (gstr_data obs p))`;

val gstr_valid_def = Define `
  gstr_valid obs (p : 'p) (size : int) <=>
    gstr_int32_in_bounds size /\
    (0 : int) <= size /\
    ((0 : int) <= gstr_minimum obs p /\
     gstr_minimum obs p <= gstr_offset obs p) /\
    gstr_offset obs p + size <= gstr_maximum obs p /\
    gstr_maximum obs p <= gstr_plength obs p`;

val gstr_access_def = Define `
  gstr_access obs (p : 'p) (relative_index : int) <=>
    gstr_minimum obs p <= gstr_offset obs p + relative_index /\
    gstr_offset obs p + relative_index < gstr_maximum obs p`;

val gstr_same_frame_def = Define `
  gstr_same_frame obs (newer : 'p) (older : 'p) <=>
    LENGTH (gstr_data obs newer) = LENGTH (gstr_data obs older) /\
    gstr_offset obs newer = gstr_offset obs older /\
    gstr_minimum obs newer = gstr_minimum obs older /\
    gstr_maximum obs newer = gstr_maximum obs older /\
    gstr_writable obs newer = gstr_writable obs older /\
    gstr_zone obs newer = gstr_zone obs older`;

val gstr_update_def = Define `
  gstr_update (f : int -> 'a) (index : int) (value : 'a) =
    \query. if query = index then value else f query`;

val gstr_value_from_def = Define `
  (gstr_value_from (m : int -> word64) (index : int) 0 =
     (0 : int)) /\
  (gstr_value_from m index (SUC count) =
     gstr_u64 (m index) +
       gstr_radix *
         gstr_value_from m (index + (1 : int)) count)`;

val gstr_value_sub_def = Define `
  gstr_value_sub (m : int -> word64) (lower : int) (upper : int) =
    gstr_value_from m lower (gstr_to_num (upper - lower))`;

val gstr_value_def = Define `
  gstr_value obs (p : 'p) (size : int) =
    gstr_value_sub
      (gstr_pelts64 obs p)
      (gstr_offset obs p)
      (gstr_offset obs p + size)`;

val gstr_valueb_def = Define `
  gstr_valueb obs (p : 'p) (nbits : int) =
    if nbits < (0 : int) then
      (0 : int)
    else
      let i = gstr_ediv nbits (64 : int) in
        gstr_value obs p i +
        gstr_ipow gstr_radix i *
          (gstr_u64
             (gstr_pelts64 obs p (gstr_offset obs p + i)) %
           gstr_ipow (2 : int) (nbits - (64 : int) * i))`;

val gstr_in_base_def = Define `
  gstr_in_base
      (base : int) (m : int -> word8) (lower : int) (upper : int) <=>
    !index : int.
      lower <= index /\ index < upper
      ==>
      (0 : int) <= gstr_u8 (m index) /\
      gstr_u8 (m index) < base`;

val gstr_svalue_from_def = Define `
  (gstr_svalue_from
      (base : int) (m : int -> word8) (lower : int) 0 =
     (0 : int)) /\
  (gstr_svalue_from base m lower (SUC count) =
     gstr_u8 (m (lower + &count)) +
       base * gstr_svalue_from base m lower count)`;

val gstr_svalue_sub_def = Define `
  gstr_svalue_sub
      (base : int) (m : int -> word8) (lower : int) (upper : int) =
    gstr_svalue_from base m lower (gstr_to_num (upper - lower))`;

val gstr_svalue_def = Define `
  gstr_svalue obs (base : int) (p : 'p) (size : int) =
    gstr_svalue_sub
      base
      (gstr_pelts8 obs p)
      (gstr_offset obs p)
      (gstr_offset obs p + size)`;

val gstr_frame_def = Define `
  gstr_frame
      obs (newer : 'p) (older : 'p) (capacity : int) <=>
    !index : int.
      index < gstr_offset obs newer \/
      gstr_offset obs newer + capacity <= index
      ==>
      gstr_pelts8 obs newer index = gstr_pelts8 obs older index`;

val gstr_loop_invariant_def = Define `
  gstr_loop_invariant
      obs64 obs8
      (up : 'p) (sp : 'q) (bits : word32) (un : word32)
      (base : word64) (sn : word32)
      (shift : word64) (j : word32) (i : word32) (sp1 : 'q) <=>
    ((0 : int) <= w2i i /\ w2i i <= w2i un) /\
    ((0 : int) <= w2i j /\ w2i j <= w2i sn) /\
    ((0 : int) < w2i j
     ==>
     (w2i sn - w2i j) * gstr_u32 bits =
       (64 : int) * w2i i + gstr_u64 shift) /\
    (((0 : int) <= gstr_u64 shift /\
      gstr_u64 shift < (64 : int)) \/
     i = un) /\
    gstr_in_base
      (gstr_u64 base)
      (gstr_pelts8 obs8 sp1)
      (gstr_offset obs8 sp1 + w2i j)
      (gstr_offset obs8 sp1 + w2i sn) /\
    ((gstr_svalue_sub
        (gstr_u64 base)
        (gstr_pelts8 obs8 sp1)
        (gstr_offset obs8 sp1 + w2i j)
        (gstr_offset obs8 sp1 + w2i sn) =
       gstr_valueb obs64 up
         ((w2i sn - w2i j) * gstr_u32 bits) /\
      (w2i sn - w2i j) * gstr_u32 bits <=
        (64 : int) * w2i un) \/
     (w2i j = (0 : int) /\
      gstr_svalue obs8 (gstr_u64 base) sp1 (w2i sn) =
        gstr_value obs64 up (w2i un))) /\
    gstr_frame obs8 sp1 sp (w2i sn)`;

val gstr_store_post_def = Define `
  gstr_store_post
      obs64 obs8
      (up : 'p) (sp : 'q) (bits : word32) (un : word32)
      (base : word64) (sn : word32)
      (j : word32) (o10 : word32)
      (next_i : word32) (next_shift : word64)
      (sp2 : 'q) <=>
    w2i o10 < w2i j /\
    ((0 : int) <= w2i next_i /\ w2i next_i <= w2i un) /\
    ((0 : int) <= w2i o10 /\ w2i o10 <= w2i sn) /\
    (w2i sn - w2i o10) * gstr_u32 bits =
      (w2i sn - w2i j) * gstr_u32 bits + gstr_u32 bits /\
    ((0 : int) < w2i o10
     ==>
     (w2i sn - w2i j) * gstr_u32 bits + gstr_u32 bits =
       (64 : int) * w2i next_i + gstr_u64 next_shift) /\
    (((0 : int) <= gstr_u64 next_shift /\
      gstr_u64 next_shift < (64 : int)) \/
     next_i = un) /\
    gstr_in_base
      (gstr_u64 base)
      (gstr_pelts8 obs8 sp2)
      (gstr_offset obs8 sp2 + w2i o10)
      (gstr_offset obs8 sp2 + w2i sn) /\
    ((gstr_svalue_sub
        (gstr_u64 base)
        (gstr_pelts8 obs8 sp2)
        (gstr_offset obs8 sp2 + w2i o10)
        (gstr_offset obs8 sp2 + w2i sn) =
       gstr_valueb obs64 up
         ((w2i sn - w2i j) * gstr_u32 bits + gstr_u32 bits) /\
      (w2i sn - w2i j) * gstr_u32 bits + gstr_u32 bits <=
        (64 : int) * w2i un) \/
     (w2i o10 = (0 : int) /\
      gstr_svalue obs8 (gstr_u64 base) sp2 (w2i sn) =
        gstr_value obs64 up (w2i un))) /\
    gstr_frame obs8 sp2 sp (w2i sn)`;

val gstr_store_byte_def = Define `
  gstr_store_byte
      obs64 obs8
      (up : 'p) (sp : 'q) (bits : word32) (un : word32)
      (base : word64) (sn : word32)
      (j : word32) (o10 : word32)
      (next_i : word32) (next_shift : word64)
      (sp1 : 'q) (byte : word8) <=>
    (gstr_access obs8 sp1 (w2i o10) /\
     gstr_writable obs8 sp1 = T) /\
    (!sp2 : 'q.
       gstr_same_frame obs8 sp2 sp1
       ==>
       gstr_pelts8 obs8 sp2 =
           gstr_update
             (gstr_pelts8 obs8 sp1)
             (gstr_offset obs8 sp2 + w2i o10)
             byte /\
       gstr_pelts8 obs8 sp2
           (gstr_offset obs8 sp2 + w2i o10) = byte
       ==>
       gstr_store_post
         obs64 obs8 up sp bits un base sn j o10
         next_i next_shift sp2)`;

val gstr_reduce_digit_def = Define `
  gstr_reduce_digit
      obs64 obs8
      (up : 'p) (sp : 'q) (bits : word32) (un : word32)
      (base : word64) (sn : word32)
      (j : word32) (o10 : word32)
      (next_i : word32) (next_shift : word64)
      (sp1 : 'q) (digit : int) <=>
    ~(gstr_u64 base = (0 : int)) /\
    gstr_uint64_in_bounds (gstr_cmod digit (gstr_u64 base)) /\
    (!sj : word64.
       gstr_u64 sj = gstr_cmod digit (gstr_u64 base)
       ==>
       ((0 : int) <= gstr_u64 sj /\
        gstr_u64 sj <= (255 : int)) /\
       (!byte : word8.
          gstr_u8 byte = gstr_u64 sj
          ==>
          gstr_store_byte
            obs64 obs8 up sp bits un base sn j o10
            next_i next_shift sp1 byte))`;

val gstr_high_limb_def = Define `
  gstr_high_limb
      obs64 obs8
      (up : 'p) (sp : 'q) (bits : word32) (un : word32)
      (base : word64) (sn : word32)
      (j : word32) (o10 : word32)
      (sp1 : 'q) (o11 : word64)
      (o14 : word32) (o15 : word64) (o17 : word64) <=>
    !high : word64.
      gstr_u64 high =
        (gstr_u64
           (gstr_pelts64 obs64 up
             (gstr_offset obs64 up + w2i o14)) *
         gstr_ipow (2 : int) (gstr_u64 o17)) %
        gstr_radix
      ==>
      gstr_uint64_in_bounds (gstr_u64 o11 + gstr_u64 high) /\
      (!o18 : word64.
         gstr_u64 o18 = gstr_u64 o11 + gstr_u64 high
         ==>
         gstr_reduce_digit
           obs64 obs8 up sp bits un base sn j o10
           o14 o15 sp1 (gstr_u64 o18))`;

val gstr_next_limb_def = Define `
  gstr_next_limb
      obs64 obs8
      (up : 'p) (sp : 'q) (bits : word32) (un : word32)
      (base : word64) (sn : word32)
      (j : word32) (o10 : word32)
      (sp1 : 'q) (o11 : word64)
      (o14 : word32) (o15 : word64) <=>
    gstr_access obs64 up (w2i o14) /\
    (!o16 : word64.
       gstr_u64 o16 = gstr_u32 bits
       ==>
       gstr_uint64_in_bounds (gstr_u64 o16 - gstr_u64 o15) /\
       (!o17 : word64.
          gstr_u64 o17 = gstr_u64 o16 - gstr_u64 o15
          ==>
          ((0 : int) <= gstr_u64 o17 /\
           gstr_u64 o17 < (64 : int)) /\
          gstr_high_limb
            obs64 obs8 up sp bits un base sn j o10
            sp1 o11 o14 o15 o17))`;

val gstr_shift_overflow_def = Define `
  gstr_shift_overflow
      obs64 obs8
      (up : 'p) (sp : 'q) (bits : word32) (un : word32)
      (base : word64) (sn : word32)
      (j : word32) (i : word32) (o10 : word32)
      (sp1 : 'q) (o11 : word64) (o13 : word64) <=>
    gstr_int32_in_bounds (w2i i + (1 : int)) /\
    (!o14 : word32.
       w2i o14 = w2i i + (1 : int)
       ==>
       if w2i o14 < w2i un then
         gstr_uint64_in_bounds (gstr_u64 o13 - (64 : int)) /\
         (!o15 : word64.
            gstr_u64 o15 = gstr_u64 o13 - (64 : int)
            ==>
            gstr_next_limb
              obs64 obs8 up sp bits un base sn j o10
              sp1 o11 o14 o15)
       else
         gstr_reduce_digit
           obs64 obs8 up sp bits un base sn j o10
           o14 o13 sp1 (gstr_u64 o11))`;

val gstr_shift_sum_def = Define `
  gstr_shift_sum
      obs64 obs8
      (up : 'p) (sp : 'q) (bits : word32) (un : word32)
      (base : word64) (sn : word32)
      (j : word32) (i : word32) (o10 : word32)
      (sp1 : 'q) (o11 : word64) (o13 : word64) <=>
    if (64 : int) <= gstr_u64 o13 then
      gstr_shift_overflow
        obs64 obs8 up sp bits un base sn j i o10 sp1 o11 o13
    else
      gstr_reduce_digit
        obs64 obs8 up sp bits un base sn j o10
        i o13 sp1 (gstr_u64 o11)`;

val gstr_positive_step_def = Define `
  gstr_positive_step
      obs64 obs8
      (up : 'p) (sp : 'q) (bits : word32) (un : word32)
      (base : word64) (sn : word32)
      (shift : word64) (j : word32) (i : word32) (sp1 : 'q) <=>
    gstr_int32_in_bounds (w2i j - (1 : int)) /\
    (!o10 : word32.
       w2i o10 = w2i j - (1 : int)
       ==>
       gstr_access obs64 up (w2i i) /\
       ((0 : int) <= gstr_u64 shift /\
        gstr_u64 shift < (64 : int)) /\
       (!o11 : word64.
          gstr_u64 o11 =
            gstr_ediv
              (gstr_u64
                (gstr_pelts64 obs64 up
                  (gstr_offset obs64 up + w2i i)))
              (gstr_ipow (2 : int) (gstr_u64 shift))
          ==>
          ~(gstr_ipow (2 : int) (gstr_u64 shift) = (0 : int)) /\
          (!o12 : word64.
             gstr_u64 o12 = gstr_u32 bits
             ==>
             gstr_uint64_in_bounds
               (gstr_u64 shift + gstr_u64 o12) /\
             (!o13 : word64.
                gstr_u64 o13 = gstr_u64 shift + gstr_u64 o12
                ==>
                gstr_shift_sum
                  obs64 obs8 up sp bits un base sn
                  j i o10 sp1 o11 o13))))`;

val gstr_finish_step_def = Define `
  gstr_finish_step
      obs64 obs8
      (up : 'p) (sp : 'q) (bits : word32) (un : word32)
      (ub : word32) (sn : word32) (sp1 : 'q) <=>
    (0 : int) <= w2i sn /\
    (!result : word32.
       gstr_u32 result = w2i sn
       ==>
       gstr_in_base
         (gstr_ipow (2 : int) (gstr_u32 bits))
         (gstr_pelts8 obs8 sp1)
         (gstr_offset obs8 sp1)
         (gstr_offset obs8 sp1 + gstr_u32 result) /\
       gstr_svalue
         obs8 (gstr_ipow (2 : int) (gstr_u32 bits))
         sp1 (gstr_u32 result) =
         gstr_value obs64 up (w2i un) /\
       ((0 : int) < gstr_u32 result /\
        gstr_u32 result <=
          gstr_ediv
            (w2i ub + gstr_u32 bits - (1 : int))
            (gstr_u32 bits)) /\
       (0 : int) <
         gstr_u8
           (gstr_pelts8 obs8 sp1 (gstr_offset obs8 sp1)) /\
       gstr_frame
         obs8 sp1 sp
         (gstr_ediv
           (w2i ub + gstr_u32 bits - (1 : int))
           (gstr_u32 bits)))`;

val gstr_loop_step_def = Define `
  gstr_loop_step
      obs64 obs8
      (up : 'p) (sp : 'q) (bits : word32) (un : word32)
      (ub : word32) (base : word64) (sn : word32)
      (shift : word64) (j : word32) (i : word32) (sp1 : 'q) <=>
    if (0 : int) < w2i j then
      gstr_positive_step
        obs64 obs8 up sp bits un base sn shift j i sp1
    else
      gstr_finish_step obs64 obs8 up sp bits un ub sn sp1`;

val gstr_loop_contract_def = Define `
  gstr_loop_contract
      obs64 obs8
      (up : 'p) (sp : 'q) (bits : word32)
      (un : word32) (ub : word32)
      (base : word64) (sn : word32) <=>
    !shift : word64.
    !j i : word32.
    !sp1 : 'q.
      gstr_same_frame obs8 sp1 sp
      ==>
      gstr_loop_invariant
        obs64 obs8 up sp bits un base sn shift j i sp1
      ==>
      gstr_loop_step
        obs64 obs8 up sp bits un ub base sn shift j i sp1`;

val gstr_initial_state_def = Define `
  gstr_initial_state
      obs64 obs8
      (up : 'p) (sp : 'q) (bits : word32)
      (un : word32) (ub : word32)
      (base : word64) (sn : word32) <=>
    (((0 : int) <= (0 : int) /\ (0 : int) <= w2i un) /\
     ((0 : int) <= w2i sn /\ w2i sn <= w2i sn) /\
     (w2i sn - w2i sn) * gstr_u32 bits = (0 : int) /\
     ((0 : int) < w2i sn
      ==>
      (0 : int) = (64 : int) * (0 : int) + (0 : int)) /\
     (((0 : int) <= (0 : int) /\ (0 : int) < (64 : int)) \/
      (0w : word32) = un) /\
     gstr_in_base
       (gstr_u64 base)
       (gstr_pelts8 obs8 sp)
       (gstr_offset obs8 sp + w2i sn)
       (gstr_offset obs8 sp + w2i sn) /\
     ((gstr_svalue_sub
         (gstr_u64 base)
         (gstr_pelts8 obs8 sp)
         (gstr_offset obs8 sp + w2i sn)
         (gstr_offset obs8 sp + w2i sn) =
        gstr_valueb obs64 up (0 : int) /\
       (0 : int) <= (64 : int) * w2i un) \/
      (w2i sn = (0 : int) /\
       gstr_svalue obs8 (gstr_u64 base) sp (w2i sn) =
         gstr_value obs64 up (w2i un)))) /\
    gstr_loop_contract obs64 obs8 up sp bits un ub base sn`;

val gstr_after_sn_def = Define `
  gstr_after_sn
      obs64 obs8
      (up : 'p) (sp : 'q) (bits : word32)
      (un : word32) (ub : word32) (sn : word32) <=>
    !o9 : word64.
      gstr_u64 o9 = gstr_u32 bits
      ==>
      (((0 : int) <= gstr_u64 o9 /\
        gstr_u64 o9 < (64 : int)) /\
       gstr_ipow (2 : int) (gstr_u64 o9) *
         gstr_u64 (1w : word64) <=
         (18446744073709551615 : int)) /\
      (!base : word64.
         gstr_u64 base =
           gstr_ipow (2 : int) (gstr_u64 o9) *
             gstr_u64 (1w : word64)
         ==>
         gstr_initial_state
           obs64 obs8 up sp bits un ub base sn)`;

val gstr_after_e_def = Define `
  gstr_after_e
      obs64 obs8
      (up : 'p) (sp : 'q) (bits : word32)
      (un : word32) (ub : word32) (e : word32) <=>
    gstr_u32 bits <= (2147483647 : int) /\
    (!o8 : word32.
       w2i o8 = gstr_u32 bits
       ==>
       ~(w2i o8 = (0 : int)) /\
       gstr_int32_in_bounds (gstr_cdiv (w2i e) (w2i o8)) /\
       (!sn : word32.
          w2i sn = gstr_cdiv (w2i e) (w2i o8)
          ==>
          gstr_after_sn obs64 obs8 up sp bits un ub sn))`;

val gstr_after_o7_def = Define `
  gstr_after_o7
      obs64 obs8
      (up : 'p) (sp : 'q) (bits : word32)
      (un : word32) (ub : word32) (o7 : word32) <=>
    gstr_int32_in_bounds (w2i o7 - (1 : int)) /\
    (!e : word32.
       w2i e = w2i o7 - (1 : int)
       ==>
       gstr_after_e obs64 obs8 up sp bits un ub e)`;

val gstr_after_o6_def = Define `
  gstr_after_o6
      obs64 obs8
      (up : 'p) (sp : 'q) (bits : word32)
      (un : word32) (ub : word32)
      (o2 : word32) (o6 : word32) <=>
    gstr_int32_in_bounds (w2i o6 + w2i o2) /\
    (!o7 : word32.
       w2i o7 = w2i o6 + w2i o2
       ==>
       gstr_after_o7 obs64 obs8 up sp bits un ub o7)`;

val gstr_after_o5_def = Define `
  gstr_after_o5
      obs64 obs8
      (up : 'p) (sp : 'q) (bits : word32)
      (un : word32) (ub : word32)
      (o2 : word32) (o3 : word32) (o5 : word32) <=>
    gstr_int32_in_bounds (w2i o5 + w2i o3) /\
    (!o6 : word32.
       w2i o6 = w2i o5 + w2i o3
       ==>
       gstr_after_o6 obs64 obs8 up sp bits un ub o2 o6)`;

val gstr_after_o4_def = Define `
  gstr_after_o4
      obs64 obs8
      (up : 'p) (sp : 'q) (bits : word32)
      (un : word32) (ub : word32)
      (o2 : word32) (o3 : word32) (o4 : word32) <=>
    gstr_int32_in_bounds ((64 : int) * w2i o4) /\
    (!o5 : word32.
       w2i o5 = (64 : int) * w2i o4
       ==>
       gstr_after_o5 obs64 obs8 up sp bits un ub o2 o3 o5)`;

val gstr_after_o3_def = Define `
  gstr_after_o3
      obs64 obs8
      (up : 'p) (sp : 'q) (bits : word32)
      (un : word32) (ub : word32)
      (o2 : word32) (o3 : word32) <=>
    gstr_int32_in_bounds (w2i un - (1 : int)) /\
    (!o4 : word32.
       w2i o4 = w2i un - (1 : int)
       ==>
       gstr_after_o4 obs64 obs8 up sp bits un ub o2 o3 o4)`;

val gstr_after_sb_def = Define `
  gstr_after_sb
      obs64 obs8
      (up : 'p) (sp : 'q) (bits : word32)
      (un : word32) (ub : word32) (sb : word64) <=>
    gstr_u32 bits <= (2147483647 : int) /\
    (!o2 : word32.
       w2i o2 = gstr_u32 bits
       ==>
       gstr_u64 sb <= (2147483647 : int) /\
       (!o3 : word32.
          w2i o3 = gstr_u64 sb
          ==>
          gstr_after_o3 obs64 obs8 up sp bits un ub o2 o3))`;

val get_str_Get_str_wmpn_get_str_bitsqtvc_statement =
  ``!obs64 :
       'p -> word64 list # (int # (int # (int # (bool # 'z)))).
    !obs8 :
       'q -> word8 list # (int # (int # (int # (bool # 'z)))).
    !un : word32.
    !up : 'p.
    !bits : word32.
    !sp : 'q.
    !ub : word32.
      (1 : int) <= w2i un ==>
      gstr_valid obs64 up (w2i un) ==>
      (1 : int) <= gstr_u32 bits ==>
      gstr_u32 bits <= (8 : int) ==>
      gstr_valid
        obs8 sp
        (gstr_ediv
          (w2i ub + gstr_u32 bits - (1 : int))
          (gstr_u32 bits)) ==>
      (0 : int) <= w2i ub ==>
      gstr_value obs64 up (w2i un) <
        gstr_ipow (2 : int) (w2i ub) ==>
      (0 : int) <
        gstr_u64
          (gstr_pelts64 obs64 up
            (gstr_offset obs64 up + w2i un - (1 : int))) ==>
      (64 : int) * w2i un + (7 : int) <=
        (2147483647 : int) ==>
      gstr_writable obs8 sp = T ==>
      gstr_int32_in_bounds (w2i un - (1 : int)) /\
      (!o1 : word32.
         w2i o1 = w2i un - (1 : int)
         ==>
         gstr_access obs64 up (w2i o1) /\
         (let um =
            gstr_pelts64 obs64 up
              (gstr_offset obs64 up + w2i o1)
          in
            (0 : int) < gstr_u64 um /\
            (!sb : word64.
               (((1 : int) <= gstr_u64 sb /\
                 gstr_u64 sb <= (64 : int)) /\
                gstr_ipow (2 : int) (gstr_u64 sb - (1 : int)) <=
                  gstr_u64 um /\
                gstr_u64 um <
                  gstr_ipow (2 : int) (gstr_u64 sb))
               ==>
               gstr_after_sb
                 obs64 obs8 up sp bits un ub sb)))``;

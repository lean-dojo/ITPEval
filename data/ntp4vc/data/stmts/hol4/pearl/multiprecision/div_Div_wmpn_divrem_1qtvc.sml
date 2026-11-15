(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/div_Div_wmpn_divrem_1qtvc: the verification condition
  for one-limb multiprecision division, including divisor normalization,
  reciprocal division, quotient-array updates, loop invariants, and the final
  quotient/remainder relation. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory listTheory wordsTheory;

val ddr1_radix_def = Define `
  ddr1_radix = (18446744073709551616 : int)`;

val ddr1_to_num_def = Define `
  ddr1_to_num (z : int) = if z < (0 : int) then 0 else Num z`;

val ddr1_u64_def = Define `
  ddr1_u64 (x : word64) = &(w2n x)`;

val ddr1_int32_in_bounds_def = Define `
  ddr1_int32_in_bounds (x : int) <=>
    -(2147483648 : int) <= x /\ x <= (2147483647 : int)`;

val ddr1_uint64_in_bounds_def = Define `
  ddr1_uint64_in_bounds (x : int) <=>
    (0 : int) <= x /\ x <= (18446744073709551615 : int)`;

val ddr1_ipow_def = Define `
  ddr1_ipow (base : int) (exponent : int) =
    base ** ddr1_to_num exponent`;

(* Data pairs an independent length with a total integer-indexed limb map. *)
val ddr1_data_def = Define `
  ddr1_data
      (obs :
        'p -> (num # (int -> word64)) # (int # (int # (int # (bool # 'z)))))
      (p : 'p) =
    FST (obs p)`;

val ddr1_offset_def = Define `
  ddr1_offset obs (p : 'p) =
    FST (SND (obs p))`;

val ddr1_minimum_def = Define `
  ddr1_minimum obs (p : 'p) =
    FST (SND (SND (obs p)))`;

val ddr1_maximum_def = Define `
  ddr1_maximum obs (p : 'p) =
    FST (SND (SND (SND (obs p))))`;

val ddr1_writable_def = Define `
  ddr1_writable obs (p : 'p) =
    FST (SND (SND (SND (SND (obs p)))))`;

val ddr1_zone_def = Define `
  ddr1_zone obs (p : 'p) =
    SND (SND (SND (SND (SND (obs p)))))`;

val ddr1_pelts_def = Define `
  ddr1_pelts obs (p : 'p) (index : int) =
    SND (ddr1_data obs p) index`;

val ddr1_plength_def = Define `
  ddr1_plength obs (p : 'p) = &(FST (ddr1_data obs p))`;

val ddr1_valid_def = Define `
  ddr1_valid obs (p : 'p) (size : int) <=>
    ddr1_int32_in_bounds size /\
    (0 : int) <= size /\
    ((0 : int) <= ddr1_minimum obs p /\
     ddr1_minimum obs p <= ddr1_offset obs p) /\
    ddr1_offset obs p + size <= ddr1_maximum obs p /\
    ddr1_maximum obs p <= ddr1_plength obs p`;

val ddr1_access_at_def = Define `
  ddr1_access_at obs (p : 'p) (relative_index : int) <=>
    ddr1_minimum obs p <= ddr1_offset obs p + relative_index /\
    ddr1_offset obs p + relative_index < ddr1_maximum obs p`;

val ddr1_same_frame_def = Define `
  ddr1_same_frame obs (newer : 'p) (older : 'p) <=>
    FST (ddr1_data obs newer) = FST (ddr1_data obs older) /\
    ddr1_offset obs newer = ddr1_offset obs older /\
    ddr1_minimum obs newer = ddr1_minimum obs older /\
    ddr1_maximum obs newer = ddr1_maximum obs older /\
    ddr1_writable obs newer = ddr1_writable obs older /\
    ddr1_zone obs newer = ddr1_zone obs older`;

val ddr1_update_def = Define `
  ddr1_update (f : int -> word64) (index : int) (limb : word64) =
    \query. if query = index then limb else f query`;

val ddr1_value_from_def = Define `
  (ddr1_value_from (m : int -> word64) (index : int) 0 = (0 : int)) /\
  (ddr1_value_from m index (SUC count) =
     ddr1_u64 (m index) +
       ddr1_radix * ddr1_value_from m (index + (1 : int)) count)`;

val ddr1_value_sub_def = Define `
  ddr1_value_sub (m : int -> word64) (lower : int) (upper : int) =
    ddr1_value_from m lower (ddr1_to_num (upper - lower))`;

val ddr1_value_def = Define `
  ddr1_value obs (p : 'p) (size : int) =
    ddr1_value_sub
      (ddr1_pelts obs p)
      (ddr1_offset obs p)
      (ddr1_offset obs p + size)`;

val ddr1_reciprocal_def = Define `
  ddr1_reciprocal (v : word64) (d : word64) <=>
    ddr1_u64 v =
      (ddr1_radix * ddr1_radix - (1 : int)) / ddr1_u64 d -
      ddr1_radix`;

val ddr1_index_bounds_def = Define `
  ddr1_index_bounds (i : word32) (msb : word32) <=>
    -(1 : int) <= w2i i /\ w2i i <= w2i msb`;

val ddr1_normalized_initial_def = Define `
  ddr1_normalized_initial
      obs (mult : int) (x : 'p) (q : 'p)
      (sz : word32) (msb : word32) (ry : word64) <=>
    ddr1_index_bounds msb msb /\
    (0 : int) < ddr1_u64 ry /\
    mult *
        ddr1_value_sub
          (ddr1_pelts obs x)
          (ddr1_offset obs x + w2i msb + (1 : int))
          (ddr1_offset obs x + w2i sz) =
      ddr1_value_sub
          (ddr1_pelts obs q)
          (ddr1_offset obs q + w2i msb + (1 : int))
          (ddr1_offset obs q + w2i sz) *
        ddr1_u64 ry +
      (0 : int) /\
    (0 : int) <= ddr1_radix - mult /\
    (0 : int) % mult = (0 : int)`;

val ddr1_normalized_invariant_def = Define `
  ddr1_normalized_invariant
      obs (mult : int) (x : 'p) (q : 'p)
      (sz : word32) (msb : word32)
      (ry : word64) (r : word64) (i : word32) <=>
    ddr1_index_bounds i msb /\
    ddr1_u64 r < ddr1_u64 ry /\
    mult *
        ddr1_value_sub
          (ddr1_pelts obs x)
          (ddr1_offset obs x + w2i i + (1 : int))
          (ddr1_offset obs x + w2i sz) =
      ddr1_value_sub
          (ddr1_pelts obs q)
          (ddr1_offset obs q + w2i i + (1 : int))
          (ddr1_offset obs q + w2i sz) *
        ddr1_u64 ry +
      ddr1_u64 r /\
    ddr1_u64 r <= ddr1_radix - mult /\
    ddr1_u64 r % mult = (0 : int)`;

val ddr1_plain_initial_def = Define `
  ddr1_plain_initial
      obs (x : 'p) (q : 'p)
      (sz : word32) (msb : word32) (y : word64) <=>
    ddr1_index_bounds msb msb /\
    (0 : int) < ddr1_u64 y /\
    ddr1_value_sub
        (ddr1_pelts obs x)
        (ddr1_offset obs x + w2i msb + (1 : int))
        (ddr1_offset obs x + w2i sz) =
      ddr1_value_sub
          (ddr1_pelts obs q)
          (ddr1_offset obs q + w2i msb + (1 : int))
          (ddr1_offset obs q + w2i sz) *
        ddr1_u64 y +
      (0 : int)`;

val ddr1_plain_invariant_def = Define `
  ddr1_plain_invariant
      obs (x : 'p) (q : 'p)
      (sz : word32) (msb : word32)
      (y : word64) (r : word64) (i : word32) <=>
    ddr1_index_bounds i msb /\
    ddr1_u64 r < ddr1_u64 y /\
    ddr1_value_sub
        (ddr1_pelts obs x)
        (ddr1_offset obs x + w2i i + (1 : int))
        (ddr1_offset obs x + w2i sz) =
      ddr1_value_sub
          (ddr1_pelts obs q)
          (ddr1_offset obs q + w2i i + (1 : int))
          (ddr1_offset obs q + w2i sz) *
        ddr1_u64 y +
      ddr1_u64 r`;

val ddr1_normalized_after_store_def = Define `
  ddr1_normalized_after_store
      obs (mult : int) (x : 'p) (q : 'p)
      (sz : word32) (msb : word32)
      (ry : word64) (remainder : word64) (i : word32) <=>
    ddr1_int32_in_bounds (w2i i - (1 : int)) /\
    (!next : word32.
       w2i next = w2i i - (1 : int)
       ==>
       w2i next < w2i i /\
       ddr1_index_bounds next msb /\
       ddr1_u64 remainder < ddr1_u64 ry /\
       mult *
           ddr1_value_sub
             (ddr1_pelts obs x)
             (ddr1_offset obs x + w2i next + (1 : int))
             (ddr1_offset obs x + w2i sz) =
         ddr1_value_sub
             (ddr1_pelts obs q)
             (ddr1_offset obs q + w2i next + (1 : int))
             (ddr1_offset obs q + w2i sz) *
           ddr1_u64 ry +
         ddr1_u64 remainder /\
       ddr1_u64 remainder <= ddr1_radix - mult /\
       ddr1_u64 remainder % mult = (0 : int))`;

val ddr1_plain_after_store_def = Define `
  ddr1_plain_after_store
      obs (x : 'p) (q : 'p)
      (sz : word32) (msb : word32)
      (y : word64) (remainder : word64) (i : word32) <=>
    ddr1_int32_in_bounds (w2i i - (1 : int)) /\
    (!next : word32.
       w2i next = w2i i - (1 : int)
       ==>
       w2i next < w2i i /\
       ddr1_index_bounds next msb /\
       ddr1_u64 remainder < ddr1_u64 y /\
       ddr1_value_sub
           (ddr1_pelts obs x)
           (ddr1_offset obs x + w2i next + (1 : int))
           (ddr1_offset obs x + w2i sz) =
         ddr1_value_sub
             (ddr1_pelts obs q)
             (ddr1_offset obs q + w2i next + (1 : int))
             (ddr1_offset obs q + w2i sz) *
           ddr1_u64 y +
         ddr1_u64 remainder)`;

val ddr1_normalized_store_def = Define `
  ddr1_normalized_store
      obs (mult : int) (x : 'p) (q1 : 'p)
      (sz : word32) (msb : word32)
      (ry : word64) (remainder : word64)
      (i : word32) (quotient : word64) <=>
    !q2 : 'p.
      ddr1_same_frame obs q2 q1
      ==>
      ddr1_pelts obs q2 =
          ddr1_update
            (ddr1_pelts obs q1)
            (ddr1_offset obs q2 + w2i i)
            quotient /\
      ddr1_pelts obs q2 (ddr1_offset obs q2 + w2i i) = quotient
      ==>
      ddr1_normalized_after_store
        obs mult x q2 sz msb ry remainder i`;

val ddr1_plain_store_def = Define `
  ddr1_plain_store
      obs (x : 'p) (q1 : 'p)
      (sz : word32) (msb : word32)
      (y : word64) (remainder : word64)
      (i : word32) (quotient : word64) <=>
    !q2 : 'p.
      ddr1_same_frame obs q2 q1
      ==>
      ddr1_pelts obs q2 =
          ddr1_update
            (ddr1_pelts obs q1)
            (ddr1_offset obs q2 + w2i i)
            quotient /\
      ddr1_pelts obs q2 (ddr1_offset obs q2 + w2i i) = quotient
      ==>
      ddr1_plain_after_store
        obs x q2 sz msb y remainder i`;

val ddr1_normalized_value_update_def = Define `
  ddr1_normalized_value_update
      obs (mult : int) (x : 'p) (q1 : 'p)
      (sz : word32) (msb : word32)
      (ry : word64) (remainder : word64)
      (i : word32) (quotient : word64) <=>
    let upper = ddr1_offset obs q1 + w2i sz in
    let middle = ddr1_offset obs q1 + (1 : int) + w2i i in
    let index = ddr1_offset obs q1 + w2i i in
    let old = ddr1_pelts obs q1 in
      (middle <= upper /\ (index < middle \/ upper <= index)) /\
      (ddr1_value_sub old middle upper =
         ddr1_value_sub (ddr1_update old index quotient) middle upper
       ==>
       ddr1_access_at obs q1 (w2i i) /\
       ddr1_writable obs q1 = T /\
       ddr1_normalized_store
         obs mult x q1 sz msb ry remainder i quotient)`;

val ddr1_plain_value_update_def = Define `
  ddr1_plain_value_update
      obs (x : 'p) (q1 : 'p)
      (sz : word32) (msb : word32)
      (y : word64) (remainder : word64)
      (i : word32) (quotient : word64) <=>
    let upper = ddr1_offset obs q1 + w2i sz in
    let middle = ddr1_offset obs q1 + (1 : int) + w2i i in
    let index = ddr1_offset obs q1 + w2i i in
    let old = ddr1_pelts obs q1 in
      (middle <= upper /\ (index < middle \/ upper <= index)) /\
      (ddr1_value_sub old middle upper =
         ddr1_value_sub (ddr1_update old index quotient) middle upper
       ==>
       ddr1_access_at obs q1 (w2i i) /\
       ddr1_writable obs q1 = T /\
       ddr1_plain_store
         obs x q1 sz msb y remainder i quotient)`;

val ddr1_normalized_division_step_def = Define `
  ddr1_normalized_division_step
      obs (mult : int) (x : 'p) (q1 : 'p)
      (sz : word32) (msb : word32)
      (ry : word64) (i : word32)
      (low : word64) (combined : word64) <=>
    !quotient remainder : word64.
      ddr1_u64 quotient * ddr1_u64 ry + ddr1_u64 remainder =
          ddr1_u64 low + ddr1_radix * ddr1_u64 combined /\
      (0 : int) <= ddr1_u64 remainder /\
      ddr1_u64 remainder < ddr1_u64 ry
      ==>
      ~(mult = (0 : int)) /\
      ddr1_normalized_value_update
        obs mult x q1 sz msb ry remainder i quotient`;

val ddr1_plain_division_step_def = Define `
  ddr1_plain_division_step
      obs (x : 'p) (q1 : 'p)
      (sz : word32) (msb : word32)
      (y : word64) (r : word64) (i : word32) <=>
    !quotient remainder : word64.
      ddr1_u64 quotient * ddr1_u64 y + ddr1_u64 remainder =
          ddr1_u64
            (ddr1_pelts obs x (ddr1_offset obs x + w2i i)) +
          ddr1_radix * ddr1_u64 r /\
      (0 : int) <= ddr1_u64 remainder /\
      ddr1_u64 remainder < ddr1_u64 y
      ==>
      ddr1_plain_value_update
        obs x q1 sz msb y remainder i quotient`;

val ddr1_normalized_combined_def = Define `
  ddr1_normalized_combined
      obs (mult : int) (x : 'p) (q1 : 'p)
      (sz : word32) (msb : word32) (i : word32)
      (ry : word64) (v : word64) (r : word64)
      (low : word64) (high : word64) <=>
    !combined : word64.
      ddr1_u64 combined = ddr1_u64 r + ddr1_u64 high
      ==>
      (ddr1_radix / (2 : int) <= ddr1_u64 ry /\
       ddr1_u64 combined < ddr1_u64 ry /\
       ddr1_reciprocal v ry) /\
      ddr1_normalized_division_step
        obs mult x q1 sz msb ry i low combined`;

val ddr1_normalized_shifted_limb_def = Define `
  ddr1_normalized_shifted_limb
      obs (mult : int) (x : 'p) (q1 : 'p)
      (sz : word32) (msb : word32) (i : word32)
      (ry : word64) (v : word64) (r : word64) (shift : word64) <=>
    !low high : word64.
      ddr1_u64 low + ddr1_radix * ddr1_u64 high =
          ddr1_ipow (2 : int) (ddr1_u64 shift) *
          ddr1_u64
            (ddr1_pelts obs x (ddr1_offset obs x + w2i i)) /\
      ddr1_u64 low % ddr1_ipow (2 : int) (ddr1_u64 shift) =
        (0 : int) /\
      ddr1_u64 low <=
        ddr1_radix - ddr1_ipow (2 : int) (ddr1_u64 shift) /\
      ddr1_u64 high < ddr1_ipow (2 : int) (ddr1_u64 shift)
      ==>
      ddr1_uint64_in_bounds (ddr1_u64 r + ddr1_u64 high) /\
      ddr1_normalized_combined
        obs mult x q1 sz msb i ry v r low high`;

val ddr1_normalized_iteration_def = Define `
  ddr1_normalized_iteration
      obs (mult : int) (x : 'p) (q1 : 'p)
      (sz : word32) (msb : word32) (clz : word32) (i : word32)
      (ry : word64) (v : word64) (r : word64) <=>
    ddr1_access_at obs x (w2i i) /\
    (0 : int) <= w2i clz /\
    (!shift : word64.
       ddr1_u64 shift = w2i clz
       ==>
       ((0 : int) < ddr1_u64 shift /\
        ddr1_u64 shift < (64 : int)) /\
       ddr1_normalized_shifted_limb
         obs mult x q1 sz msb i ry v r shift)`;

val ddr1_normalized_finish_def = Define `
  ddr1_normalized_finish
      obs (x : 'p) (q1 : 'p)
      (sz : word32) (clz : word32) (y : word64) (r : word64) <=>
    (0 : int) <= w2i clz /\
    (!shift : word64.
       ddr1_u64 shift = w2i clz
       ==>
       (((0 : int) <= ddr1_u64 shift /\
         ddr1_u64 shift < (64 : int)) /\
        ddr1_u64 r % ddr1_ipow (2 : int) (ddr1_u64 shift) =
          (0 : int)) /\
       (!res : word64.
          ddr1_u64 r =
            ddr1_ipow (2 : int) (ddr1_u64 shift) * ddr1_u64 res
          ==>
          (0 : int) <= w2i clz /\
          (!shift_again : word64.
             ddr1_u64 shift_again = w2i clz
             ==>
             (((0 : int) <= ddr1_u64 shift_again /\
               ddr1_u64 shift_again < (64 : int)) /\
              ddr1_u64 r %
                  ddr1_ipow (2 : int) (ddr1_u64 shift_again) =
                (0 : int)) /\
             (!result : word64.
                ddr1_u64 r =
                  ddr1_ipow (2 : int) (ddr1_u64 shift_again) *
                  ddr1_u64 result
                ==>
                ddr1_value obs x (w2i sz) =
                    ddr1_value obs q1 (w2i sz) * ddr1_u64 y +
                    ddr1_u64 result /\
                ddr1_u64 result < ddr1_u64 y))))`;

val ddr1_normalized_loop_body_def = Define `
  ddr1_normalized_loop_body
      obs (mult : int) (x : 'p) (q1 : 'p)
      (sz : word32) (msb : word32) (clz : word32)
      (y : word64) (ry : word64) (v : word64)
      (r : word64) (i : word32) <=>
    if (0 : int) <= w2i i then
      ddr1_normalized_iteration
        obs mult x q1 sz msb clz i ry v r
    else
      ddr1_normalized_finish obs x q1 sz clz y r`;

val ddr1_normalized_all_loops_def = Define `
  ddr1_normalized_all_loops
      obs (mult : int) (x : 'p) (q : 'p)
      (sz : word32) (msb : word32) (clz : word32)
      (y : word64) (ry : word64) (v : word64) <=>
    !r : word64. !i : word32. !q1 : 'p.
      ddr1_same_frame obs q1 q
      ==>
      ddr1_normalized_invariant obs mult x q1 sz msb ry r i
      ==>
      ddr1_normalized_loop_body
        obs mult x q1 sz msb clz y ry v r i`;

val ddr1_normalized_reciprocal_def = Define `
  ddr1_normalized_reciprocal
      obs (mult : int) (x : 'p) (q : 'p)
      (sz : word32) (msb : word32) (clz : word32)
      (y : word64) (ry : word64) <=>
    !v : word64.
      ddr1_reciprocal v ry
      ==>
      ddr1_normalized_initial obs mult x q sz msb ry /\
      ddr1_normalized_all_loops obs mult x q sz msb clz y ry v`;

val ddr1_normalized_divisor_def = Define `
  ddr1_normalized_divisor
      obs (mult : int) (x : 'p) (q : 'p)
      (sz : word32) (msb : word32) (clz : word32)
      (y : word64) (shift : word64) <=>
    !ry : word64.
      ddr1_u64 ry =
        ddr1_ipow (2 : int) (ddr1_u64 shift) * ddr1_u64 y
      ==>
      ddr1_radix / (2 : int) <= ddr1_u64 ry /\
      ddr1_normalized_reciprocal
        obs mult x q sz msb clz y ry`;

val ddr1_normalized_branch_def = Define `
  ddr1_normalized_branch
      obs (x : 'p) (q : 'p)
      (sz : word32) (msb : word32) (clz : word32) (y : word64) <=>
    let mult = ddr1_ipow (2 : int) (w2i clz) in
      (0 : int) <= w2i clz /\
      (!shift : word64.
         ddr1_u64 shift = w2i clz
         ==>
         (((0 : int) <= ddr1_u64 shift /\
           ddr1_u64 shift < (64 : int)) /\
          ddr1_ipow (2 : int) (ddr1_u64 shift) * ddr1_u64 y <=
            (18446744073709551615 : int)) /\
         ddr1_normalized_divisor
           obs mult x q sz msb clz y shift)`;

val ddr1_plain_iteration_def = Define `
  ddr1_plain_iteration
      obs (x : 'p) (q1 : 'p)
      (sz : word32) (msb : word32)
      (y : word64) (v : word64) (r : word64) (i : word32) <=>
    ddr1_access_at obs x (w2i i) /\
    (ddr1_radix / (2 : int) <= ddr1_u64 y /\
     ddr1_u64 r < ddr1_u64 y /\
     ddr1_reciprocal v y) /\
    ddr1_plain_division_step obs x q1 sz msb y r i`;

val ddr1_plain_finish_def = Define `
  ddr1_plain_finish
      obs (x : 'p) (q1 : 'p)
      (sz : word32) (y : word64) (r : word64) <=>
    ddr1_value obs x (w2i sz) =
        ddr1_value obs q1 (w2i sz) * ddr1_u64 y +
        ddr1_u64 r /\
    ddr1_u64 r < ddr1_u64 y`;

val ddr1_plain_loop_body_def = Define `
  ddr1_plain_loop_body
      obs (x : 'p) (q1 : 'p)
      (sz : word32) (msb : word32)
      (y : word64) (v : word64) (r : word64) (i : word32) <=>
    if (0 : int) <= w2i i then
      ddr1_plain_iteration obs x q1 sz msb y v r i
    else
      ddr1_plain_finish obs x q1 sz y r`;

val ddr1_plain_all_loops_def = Define `
  ddr1_plain_all_loops
      obs (x : 'p) (q : 'p)
      (sz : word32) (msb : word32)
      (y : word64) (v : word64) <=>
    !r : word64. !i : word32. !q1 : 'p.
      ddr1_same_frame obs q1 q
      ==>
      ddr1_plain_invariant obs x q1 sz msb y r i
      ==>
      ddr1_plain_loop_body obs x q1 sz msb y v r i`;

val ddr1_plain_branch_def = Define `
  ddr1_plain_branch
      obs (x : 'p) (q : 'p)
      (sz : word32) (msb : word32) (y : word64) <=>
    ddr1_radix / (2 : int) <= ddr1_u64 y /\
    (!v : word64.
       ddr1_reciprocal v y
       ==>
       ddr1_plain_initial obs x q sz msb y /\
       ddr1_plain_all_loops obs x q sz msb y v)`;

val ddr1_clz_premise_def = Define `
  ddr1_clz_premise (clz : word32) (y : word64) <=>
    ddr1_ipow (2 : int) (w2i clz) * ddr1_u64 y <=
      (18446744073709551615 : int) /\
    (18446744073709551615 : int) <
      (2 : int) * ddr1_ipow (2 : int) (w2i clz) * ddr1_u64 y /\
    (0 : int) <= w2i clz /\
    w2i clz < (64 : int)`;

val ddr1_after_msb_def = Define `
  ddr1_after_msb
      obs (x : 'p) (q : 'p)
      (sz : word32) (msb : word32) (y : word64) <=>
    (0 : int) < ddr1_u64 y /\
    (!clz : word32.
       ddr1_clz_premise clz y
       ==>
       if (0 : int) < w2i clz then
         ddr1_normalized_branch obs x q sz msb clz y
       else
         ddr1_plain_branch obs x q sz msb y)`;

val div_Div_wmpn_divrem_1qtvc_statement =
  ``!obs :
       'p -> (num # (int -> word64)) # (int # (int # (int # (bool # 'z)))).
    !x : 'p. !sz : word32. !q : 'p. !y : word64.
      ddr1_valid obs x (w2i sz) /\
      ddr1_valid obs q (w2i sz) /\
      ddr1_writable obs q = T /\
      (0 : int) < w2i sz /\
      (0 : int) < ddr1_u64 y
      ==>
      ddr1_int32_in_bounds (w2i sz - (1 : int)) /\
      (!msb : word32.
         w2i msb = w2i sz - (1 : int)
         ==>
         ddr1_after_msb obs x q sz msb y)``;

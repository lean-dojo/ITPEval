(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/div_Div_wmpn_divrem_2qtvc: the verification condition
  for two-limb multiprecision division, including reciprocal normalization,
  quotient-loop invariants, pointer updates, and the final quotient/remainder
  relation. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory listTheory wordsTheory;

val ddr2_radix_def = Define `
  ddr2_radix = (18446744073709551616 : int)`;

val ddr2_half_radix_def = Define `
  ddr2_half_radix = (9223372036854775808 : int)`;

val ddr2_to_num_def = Define `
  ddr2_to_num (z : int) = if z < (0 : int) then 0 else Num z`;

val ddr2_uint_def = Define `
  ddr2_uint (w : word64) = &(w2n w)`;

val ddr2_int32_in_bounds_def = Define `
  ddr2_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val ddr2_power_def = Define `
  ddr2_power (base : int) (exponent : int) =
    base ** ddr2_to_num exponent`;

(* Data pairs an independent length with a total integer-indexed limb map. *)
val ddr2_data_def = Define `
  ddr2_data
      (obs :
        'p -> (num # (int -> word64)) # (int # (int # (int # (bool # 'z)))))
      (p : 'p) =
    FST (obs p)`;

val ddr2_offset_def = Define `
  ddr2_offset obs (p : 'p) =
    FST (SND (obs p))`;

val ddr2_minimum_def = Define `
  ddr2_minimum obs (p : 'p) =
    FST (SND (SND (obs p)))`;

val ddr2_maximum_def = Define `
  ddr2_maximum obs (p : 'p) =
    FST (SND (SND (SND (obs p))))`;

val ddr2_writable_def = Define `
  ddr2_writable obs (p : 'p) =
    FST (SND (SND (SND (SND (obs p)))))`;

val ddr2_zone_def = Define `
  ddr2_zone obs (p : 'p) =
    SND (SND (SND (SND (SND (obs p)))))`;

val ddr2_pelts_def = Define `
  ddr2_pelts obs (p : 'p) (index : int) =
    SND (ddr2_data obs p) index`;

val ddr2_plength_def = Define `
  ddr2_plength obs (p : 'p) = &(FST (ddr2_data obs p))`;

val ddr2_valid_def = Define `
  ddr2_valid obs (p : 'p) (size : int) <=>
    ddr2_int32_in_bounds size /\
    (0 : int) <= size /\
    ((0 : int) <= ddr2_minimum obs p /\
     ddr2_minimum obs p <= ddr2_offset obs p) /\
    ddr2_offset obs p + size <= ddr2_maximum obs p /\
    ddr2_maximum obs p <= ddr2_plength obs p`;

val ddr2_access_at_def = Define `
  ddr2_access_at obs (p : 'p) (relative_index : int) <=>
    ddr2_minimum obs p <= ddr2_offset obs p + relative_index /\
    ddr2_offset obs p + relative_index < ddr2_maximum obs p`;

val ddr2_same_frame_def = Define `
  ddr2_same_frame obs (newer : 'p) (older : 'p) <=>
    FST (ddr2_data obs newer) = FST (ddr2_data obs older) /\
    ddr2_offset obs newer = ddr2_offset obs older /\
    ddr2_minimum obs newer = ddr2_minimum obs older /\
    ddr2_maximum obs newer = ddr2_maximum obs older /\
    ddr2_writable obs newer = ddr2_writable obs older /\
    ddr2_zone obs newer = ddr2_zone obs older`;

val ddr2_shift_view_def = Define `
  ddr2_shift_view
      obs (shifted : 'p) (original : 'p) (delta : int) <=>
    ddr2_offset obs shifted = ddr2_offset obs original + delta /\
    ddr2_plength obs shifted = ddr2_plength obs original /\
    ddr2_pelts obs shifted = ddr2_pelts obs original /\
    ddr2_data obs shifted = ddr2_data obs original /\
    ddr2_minimum obs shifted = ddr2_minimum obs original /\
    ddr2_maximum obs shifted = ddr2_maximum obs original /\
    ddr2_zone obs shifted = ddr2_zone obs original /\
    ddr2_writable obs shifted = ddr2_writable obs original`;

val ddr2_update_def = Define `
  ddr2_update (f : int -> word64) (index : int) (limb : word64) =
    \query. if query = index then limb else f query`;

val ddr2_value_from_def = Define `
  (ddr2_value_from (f : int -> word64) (index : int) 0 = (0 : int)) /\
  (ddr2_value_from f index (SUC count) =
     ddr2_uint (f index) +
       ddr2_radix *
         ddr2_value_from f (index + (1 : int)) count)`;

val ddr2_value_sub_def = Define `
  ddr2_value_sub (f : int -> word64) (lower : int) (upper : int) =
    ddr2_value_from f lower (ddr2_to_num (upper - lower))`;

val ddr2_value_def = Define `
  ddr2_value obs (p : 'p) (size : int) =
    ddr2_value_sub
      (ddr2_pelts obs p)
      (ddr2_offset obs p)
      (ddr2_offset obs p + size)`;

val ddr2_reciprocal_3by2_def = Define `
  ddr2_reciprocal_3by2
      (v : word64) (dh : word64) (dl : word64) <=>
    ddr2_uint v =
      (ddr2_radix * ddr2_radix * ddr2_radix - (1 : int)) /
        (ddr2_uint dl + ddr2_radix * ddr2_uint dh) -
      ddr2_radix`;

val ddr2_loop_state_def = Define `
  ddr2_loop_state
      obs (x : 'p) (y : 'p) (qview : 'p) (xview : 'p)
      (sx : word32) (i : word32)
      (dl : word64) (dh : word64) (qh : word64)
      (rl : word64) (rh : word64) <=>
    ((0 : int) <= w2i i /\ w2i i <= w2i sx - (2 : int)) /\
    ddr2_offset obs xview = ddr2_offset obs x + w2i i /\
    ddr2_plength obs xview = ddr2_plength obs x /\
    ddr2_minimum obs xview = ddr2_minimum obs x /\
    ddr2_maximum obs xview = ddr2_maximum obs x /\
    ddr2_pelts obs xview = ddr2_pelts obs x /\
    ddr2_writable obs xview = T /\
    ddr2_value obs x (w2i sx) =
      (ddr2_value_sub
         (ddr2_pelts obs qview)
         (ddr2_offset obs qview + w2i i)
         (ddr2_offset obs qview + w2i sx - (2 : int)) +
       ddr2_uint qh *
         ddr2_power ddr2_radix
           (w2i sx - (2 : int) - w2i i)) *
        ddr2_value obs y (2 : int) *
        ddr2_power ddr2_radix (w2i i) +
      ddr2_value obs x (w2i i) +
      ddr2_power ddr2_radix (w2i i) *
        (ddr2_uint rl + ddr2_radix * ddr2_uint rh) /\
    ddr2_uint rl + ddr2_radix * ddr2_uint rh <
      ddr2_uint dl + ddr2_radix * ddr2_uint dh`;

val ddr2_final_post_def = Define `
  ddr2_final_post
      obs (x : 'p) (y : 'p) (q1 : 'p) (x2 : 'p)
      (sx : word32) (qh : word64) <=>
    ddr2_value obs x (w2i sx) =
      (ddr2_value obs q1 (w2i sx - (2 : int)) +
       ddr2_power ddr2_radix (w2i sx - (2 : int)) *
         ddr2_uint qh) *
        ddr2_value obs y (2 : int) +
      ddr2_value obs x2 (2 : int) /\
    ddr2_value obs x2 (2 : int) < ddr2_value obs y (2 : int) /\
    (0 : int) <= ddr2_uint qh /\ ddr2_uint qh <= (1 : int)`;

val ddr2_finish_loop_def = Define `
  ddr2_finish_loop
      obs (x : 'p) (y : 'p) (q1 : 'p)
      (sx : word32) (qh : word64)
      (rl : word64) (rh : word64) <=>
    (ddr2_access_at obs x (1 : int) /\
     ddr2_writable obs x = T) /\
    (!x1 : 'p.
       ddr2_same_frame obs x1 x
       ==>
       ddr2_pelts obs x1 =
           ddr2_update
             (ddr2_pelts obs x)
             (ddr2_offset obs x1 + (1 : int))
             rh /\
       ddr2_pelts obs x1 (ddr2_offset obs x1 + (1 : int)) = rh
       ==>
       (ddr2_access_at obs x1 (0 : int) /\
        ddr2_writable obs x1 = T) /\
       (!x2 : 'p.
          ddr2_same_frame obs x2 x1
          ==>
          ddr2_pelts obs x2 =
            ddr2_update
              (ddr2_pelts obs x1)
              (ddr2_offset obs x2)
              rl
          ==>
          ddr2_final_post obs x y q1 x2 sx qh))`;

val ddr2_after_quotient_store_def = Define `
  ddr2_after_quotient_store
      obs (x : 'p) (y : 'p) (q1 : 'p) (xnext : 'p)
      (sx : word32) (i : word32)
      (dl : word64) (dh : word64) (qh : word64)
      (qu : word64) (r0 : word64) (r1 : word64) <=>
    ddr2_int32_in_bounds (w2i i - (1 : int)) /\
    (!next : word32.
       w2i next = w2i i - (1 : int)
       ==>
       (ddr2_access_at obs q1 (w2i next) /\
        ddr2_writable obs q1 = T) /\
       (!q2 : 'p.
          ddr2_same_frame obs q2 q1
          ==>
          ddr2_pelts obs q2 =
              ddr2_update
                (ddr2_pelts obs q1)
                (ddr2_offset obs q2 + w2i next)
                qu /\
          ddr2_pelts obs q2 (ddr2_offset obs q2 + w2i next) = qu
          ==>
          w2i next < w2i i /\
          ddr2_loop_state
            obs x y q2 xnext sx next dl dh qh r0 r1))`;

val ddr2_division_step_def = Define `
  ddr2_division_step
      obs (x : 'p) (y : 'p) (q1 : 'p) (xnext : 'p)
      (sx : word32) (i : word32)
      (dl : word64) (dh : word64) (qh : word64)
      (rl : word64) (rh : word64) <=>
    !qu r0 r1 : word64.
      ddr2_uint qu * ddr2_uint dl +
          ddr2_radix * ddr2_uint qu * ddr2_uint dh +
          ddr2_uint r0 + ddr2_radix * ddr2_uint r1 =
        ddr2_uint (ddr2_pelts obs xnext (ddr2_offset obs xnext)) +
          ddr2_radix * ddr2_uint rl +
          ddr2_radix * ddr2_radix * ddr2_uint rh /\
      (0 : int) <= ddr2_uint r0 + ddr2_radix * ddr2_uint r1 /\
      ddr2_uint r0 + ddr2_radix * ddr2_uint r1 <
        ddr2_uint dl + ddr2_radix * ddr2_uint dh
      ==>
      ddr2_after_quotient_store
        obs x y q1 xnext sx i dl dh qh qu r0 r1`;

val ddr2_positive_loop_def = Define `
  ddr2_positive_loop
      obs (x : 'p) (y : 'p) (q1 : 'p) (xp : 'p)
      (sx : word32) (i : word32)
      (dl : word64) (dh : word64) (dinv : word64)
      (qh : word64) (rl : word64) (rh : word64) <=>
    (ddr2_minimum obs xp <=
       ddr2_offset obs xp + -(1 : int) /\
     ddr2_offset obs xp + -(1 : int) <=
       ddr2_maximum obs xp) /\
    (!xnext : 'p.
       ddr2_shift_view obs xnext xp (-(1 : int))
       ==>
       ddr2_access_at obs xnext (0 : int) /\
       (ddr2_half_radix <= ddr2_uint dh /\
        ddr2_reciprocal_3by2 dinv dh dl /\
        ddr2_uint rl + ddr2_radix * ddr2_uint rh <
          ddr2_uint dl + ddr2_radix * ddr2_uint dh) /\
       ddr2_division_step
         obs x y q1 xnext sx i dl dh qh rl rh)`;

val ddr2_loop_body_def = Define `
  ddr2_loop_body
      obs (x : 'p) (y : 'p) (q1 : 'p) (xp : 'p)
      (sx : word32) (i : word32)
      (dl : word64) (dh : word64) (dinv : word64)
      (qh : word64) (rl : word64) (rh : word64) <=>
    if (0 : int) < w2i i then
      ddr2_positive_loop
        obs x y q1 xp sx i dl dh dinv qh rl rh
    else
      ddr2_finish_loop obs x y q1 sx qh rl rh`;

val ddr2_all_loops_def = Define `
  ddr2_all_loops
      obs (x : 'p) (y : 'p) (q : 'p)
      (sx : word32) (dl : word64) (dh : word64)
      (dinv : word64) (qh : word64) <=>
    !i : word32. !rl rh : word64. !xp q1 : 'p.
      ddr2_same_frame obs q1 q
      ==>
      ddr2_loop_state obs x y q1 xp sx i dl dh qh rl rh
      ==>
      ddr2_loop_body
        obs x y q1 xp sx i dl dh dinv qh rl rh`;

val ddr2_adjusted_limbs_def = Define `
  ddr2_adjusted_limbs
      (dh : word64) (dl : word64)
      (xh : word64) (xl : word64)
      (rh : word64) (rl : word64) (qh : word64) <=>
    ?borrow : bool.
      (if ddr2_uint dh <= ddr2_uint xh then
         if ddr2_uint dh < ddr2_uint xh then
           borrow = T
         else
           borrow =
             (if ddr2_uint dl <= ddr2_uint xl then T else F)
       else
         borrow = F) /\
      (if borrow = T then
         ?d : word64.
           (ddr2_uint rl - ddr2_radix * ddr2_uint d =
                ddr2_uint xl - ddr2_uint dl - (0 : int) /\
            (0 : int) <= ddr2_uint d /\
            ddr2_uint d <= (1 : int)) /\
           (?d1 : word64.
              (ddr2_uint rh - ddr2_radix * ddr2_uint d1 =
                   ddr2_uint xh - ddr2_uint dh - ddr2_uint d /\
               (0 : int) <= ddr2_uint d1 /\
               ddr2_uint d1 <= (1 : int)) /\
              qh = (1w : word64))
       else
         (rh = xh /\ rl = xl) /\ qh = (0w : word64))`;

val ddr2_initial_borrow_check_def = Define `
  ddr2_initial_borrow_check
      (dh : word64) (dl : word64)
      (xh : word64) (xl : word64) <=>
    (if ddr2_uint dh <= ddr2_uint xh then
       if ddr2_uint dh < ddr2_uint xh then
         T
       else
         T = (if ddr2_uint dl <= ddr2_uint xl then T else F)
     else
       T = F)
    ==>
    (((0 : int) <= (0 : int) /\ (0 : int) <= (1 : int)) /\
     (!r0 b : word64.
        ddr2_uint r0 - ddr2_radix * ddr2_uint b =
            ddr2_uint xl - ddr2_uint dl - (0 : int) /\
        (0 : int) <= ddr2_uint b /\
        ddr2_uint b <= (1 : int)
        ==>
        (0 : int) <= ddr2_uint b /\
        ddr2_uint b <= (1 : int)))`;

val ddr2_reciprocal_continuation_def = Define `
  ddr2_reciprocal_continuation
      obs (x : 'p) (y : 'p) (q : 'p) (xview : 'p)
      (sx : word32) (top : word32)
      (dl : word64) (dh : word64)
      (xl : word64) (xh : word64)
      (dinv : word64) <=>
    ddr2_initial_borrow_check dh dl xh xl /\
    (!rh rl qh : word64.
       ddr2_adjusted_limbs dh dl xh xl rh rl qh
       ==>
       ddr2_loop_state
         obs x y q xview sx top dl dh qh rl rh /\
       ddr2_all_loops obs x y q sx dl dh dinv qh)`;

val ddr2_after_top_index_def = Define `
  ddr2_after_top_index
      obs (x : 'p) (y : 'p) (q : 'p) (xview : 'p)
      (sx : word32) (top : word32)
      (dl : word64) (dh : word64)
      (xl : word64) (xh : word64) <=>
    ddr2_half_radix <= ddr2_uint dh /\
    (!dinv : word64.
       ddr2_reciprocal_3by2 dinv dh dl
       ==>
       ddr2_reciprocal_continuation
         obs x y q xview sx top dl dh xl xh dinv)`;

val ddr2_shifted_dividend_def = Define `
  ddr2_shifted_dividend
      obs (x : 'p) (y : 'p) (q : 'p) (xview : 'p)
      (sx : word32) (top : word32) <=>
    ddr2_access_at obs y (1 : int) /\
    let dh : word64 =
      ddr2_pelts obs y (ddr2_offset obs y + (1 : int))
    in
      ddr2_access_at obs y (0 : int) /\
      let dl : word64 =
        ddr2_pelts obs y (ddr2_offset obs y)
      in
        ddr2_access_at obs xview (1 : int) /\
        let xh : word64 =
          ddr2_pelts obs xview
            (ddr2_offset obs xview + (1 : int))
        in
          ddr2_access_at obs xview (0 : int) /\
          let xl : word64 =
            ddr2_pelts obs xview (ddr2_offset obs xview)
          in
            ddr2_int32_in_bounds (w2i sx - (2 : int)) /\
            (!top_again : word32.
               w2i top_again = w2i sx - (2 : int)
               ==>
               ddr2_after_top_index
                 obs x y q xview sx top_again dl dh xl xh)`;

val div_Div_wmpn_divrem_2qtvc_statement =
  ``!obs :
       'p -> (num # (int -> word64)) # (int # (int # (int # (bool # 'z)))).
    !sx : word32. !x y q : 'p.
      (2 : int) <= w2i sx /\
      ddr2_valid obs x (w2i sx) /\
      ddr2_valid obs y (2 : int) /\
      ddr2_valid obs q (w2i sx - (2 : int)) /\
      ddr2_half_radix <=
        ddr2_uint
          (ddr2_pelts obs y (ddr2_offset obs y + (1 : int))) /\
      ddr2_writable obs q = T /\
      ddr2_writable obs x = T
      ==>
      ddr2_int32_in_bounds (w2i sx - (2 : int)) /\
      (!top : word32.
         w2i top = w2i sx - (2 : int)
         ==>
         (ddr2_minimum obs x <=
            ddr2_offset obs x + w2i top /\
          ddr2_offset obs x + w2i top <=
            ddr2_maximum obs x) /\
         (!xview : 'p.
            ddr2_shift_view obs xview x (w2i top)
            ==>
            ddr2_shifted_dividend obs x y q xview sx top))``;

(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/powm_Powm_wmpn_redc_1qtvc: the verification condition
  for one-limb Montgomery reduction of a double-width multiprecision integer,
  including its loop invariant and final conditional subtraction. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory listTheory wordsTheory;

val _ = type_abbrev
  ("wr1_ptr",
   ``:word64 list # (int # (int # (int # (bool # 'z))))``);

val wr1_radix_def = Define
  `wr1_radix = (18446744073709551616 : int)`;

val wr1_u64_def = Define
  `wr1_u64 (x : word64) = &(w2n x)`;

val wr1_word32_in_bounds_def = Define
  `wr1_word32_in_bounds (x:int) <=>
     -(2147483648 : int) <= x /\ x <= (2147483647 : int)`;

val wr1_to_num_def = Define
  `wr1_to_num (z:int) = if z < (0 : int) then 0 else Num z`;

val wr1_ipow_def = Define
  `wr1_ipow (base:int) (exponent:int) =
     base ** (wr1_to_num exponent)`;

val wr1_data_def = Define
  `wr1_data (p: 'z wr1_ptr) = FST p`;

val wr1_offset_def = Define
  `wr1_offset (p: 'z wr1_ptr) = FST (SND p)`;

val wr1_minimum_def = Define
  `wr1_minimum (p: 'z wr1_ptr) = FST (SND (SND p))`;

val wr1_maximum_def = Define
  `wr1_maximum (p: 'z wr1_ptr) = FST (SND (SND (SND p)))`;

val wr1_writable_def = Define
  `wr1_writable (p: 'z wr1_ptr) = FST (SND (SND (SND (SND p))))`;

val wr1_zone_def = Define
  `wr1_zone (p: 'z wr1_ptr) = SND (SND (SND (SND (SND p))))`;

val wr1_pelt_def = Define
  `wr1_pelt (p: 'z wr1_ptr) (i:int) =
     if wr1_to_num i < LENGTH (wr1_data p)
     then EL (wr1_to_num i) (wr1_data p)
     else (0w : word64)`;

val wr1_plength_def = Define
  `wr1_plength (p: 'z wr1_ptr) = (&(LENGTH (wr1_data p)):int)`;

val wr1_valid_def = Define
  `wr1_valid (p: 'z wr1_ptr) (size:int) <=>
     wr1_word32_in_bounds size /\
     (0 : int) <= size /\
     (0 : int) <= wr1_minimum p /\
     wr1_minimum p <= wr1_offset p /\
     wr1_offset p + size <= wr1_maximum p /\
     wr1_maximum p <= wr1_plength p`;

val wr1_value_from_def = Define
  `(wr1_value_from (m:int -> word64) (index:int) 0 = (0 : int)) /\
   (wr1_value_from m index (SUC count) =
      wr1_u64 (m index) +
      wr1_radix * wr1_value_from m (index + (1 : int)) count)`;

val wr1_value_def = Define
  `wr1_value (p: 'z wr1_ptr) (size:int) =
     wr1_value_from
       (wr1_pelt p)
       (wr1_offset p)
       (wr1_to_num size)`;

val wr1_redc_def = Define
  `wr1_redc (ur:int) (u:int) (n:int) (modulus:int) <=>
     ur % modulus =
     (wr1_ipow wr1_radix n * u) % modulus`;

val wr1_same_pelts_def = Define
  `wr1_same_pelts (left: 'z wr1_ptr) (right: 'z wr1_ptr) <=>
     !index:int. wr1_pelt left index = wr1_pelt right index`;

val wr1_same_metadata_def = Define
  `wr1_same_metadata (left: 'z wr1_ptr) (right: 'z wr1_ptr) <=>
     wr1_plength left = wr1_plength right /\
     wr1_offset left = wr1_offset right /\
     wr1_minimum left = wr1_minimum right /\
     wr1_maximum left = wr1_maximum right /\
     wr1_writable left = wr1_writable right /\
     wr1_zone left = wr1_zone right`;

val wr1_shift_state_def = Define
  `wr1_shift_state (newp: 'z wr1_ptr) (oldp: 'z wr1_ptr) (amount:int) <=>
     wr1_offset newp = wr1_offset oldp + amount /\
     wr1_plength newp = wr1_plength oldp /\
     wr1_same_pelts newp oldp /\
     wr1_data newp = wr1_data oldp /\
     wr1_minimum newp = wr1_minimum oldp /\
     wr1_maximum newp = wr1_maximum oldp /\
     wr1_zone newp = wr1_zone oldp /\
     wr1_writable newp = wr1_writable oldp`;

val wr1_unchanged_outside_def = Define
  `wr1_unchanged_outside
     (newp: 'z wr1_ptr) (oldp: 'z wr1_ptr) (start:int) (size:int) <=>
     !index:int.
       index < start \/ start + size <= index
       ==> wr1_pelt newp index = wr1_pelt oldp index`;

val wr1_updated_pelts_def = Define
  `wr1_updated_pelts
     (newp: 'z wr1_ptr) (oldp: 'z wr1_ptr) (update_index:int)
     (update_value:word64) <=>
     !index:int.
       wr1_pelt newp index =
       if index = update_index then update_value else wr1_pelt oldp index`;

val wr1_final_rp2_premise_def = Define
  `wr1_final_rp2_premise
     (n:word32) (up: 'z wr1_ptr) (rp1: 'z wr1_ptr) (rp2: 'z wr1_ptr)
     (o6:word64) (vm:int) <=>
     wr1_value rp2 (w2i n) % vm =
       (wr1_value rp1 (w2i n) +
        wr1_ipow wr1_radix (w2i n) * wr1_u64 o6) % vm /\
     wr1_unchanged_outside rp2 rp1 (wr1_offset rp2) (w2i n) /\
     (wr1_value up ((2 : int) * w2i n) <
        wr1_ipow wr1_radix (w2i n) * vm
      ==> wr1_value rp2 (w2i n) < (2 : int) * vm)`;

val wr1_final_rp2_conclusion_def = Define
  `wr1_final_rp2_conclusion
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr) (rp2: 'z wr1_ptr) <=>
     wr1_redc
       (wr1_value up ((2 : int) * w2i n))
       (wr1_value rp2 (w2i n))
       (w2i n)
       (wr1_value mp (w2i n)) /\
     wr1_unchanged_outside rp2 rp (wr1_offset rp2) (w2i n) /\
     (wr1_value up ((2 : int) * w2i n) <
        wr1_ipow wr1_radix (w2i n) * wr1_value mp (w2i n)
      ==> wr1_value rp2 (w2i n) <
          (2 : int) * wr1_value mp (w2i n))`;

val wr1_final_rp2_body_def = Define
  `wr1_final_rp2_body
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (rp1: 'z wr1_ptr) (o6:word64) (vm:int) (rp2: 'z wr1_ptr) <=>
     wr1_same_metadata rp2 rp1
     ==> wr1_final_rp2_premise n up rp1 rp2 o6 vm
     ==> wr1_final_rp2_conclusion n up rp mp rp2`;

val wr1_all_final_rp2_def = Define
  `wr1_all_final_rp2
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (rp1: 'z wr1_ptr) (o6:word64) (vm:int) <=>
     !rp2: 'z wr1_ptr. wr1_final_rp2_body n up rp mp rp1 o6 vm rp2`;

val wr1_sub_b_body_def = Define
  `wr1_sub_b_body
     (n:word32) (up: 'z wr1_ptr) (mp: 'z wr1_ptr) (rp1: 'z wr1_ptr)
     (rp2: 'z wr1_ptr) (o6:word64) (vm:int) (b:word64) <=>
     (wr1_value rp2 (w2i n) -
        wr1_ipow wr1_radix (w2i n) * wr1_u64 b =
        wr1_value rp1 (w2i n) - wr1_value mp (w2i n) /\
      (0 : int) <= wr1_u64 b /\ wr1_u64 b <= (1 : int) /\
      wr1_unchanged_outside rp2 rp1 (wr1_offset rp2) (w2i n))
     ==>
     (wr1_value rp2 (w2i n) % vm =
        (wr1_value rp1 (w2i n) +
         wr1_ipow wr1_radix (w2i n) * wr1_u64 o6) % vm /\
      wr1_unchanged_outside rp2 rp1 (wr1_offset rp2) (w2i n) /\
      (wr1_value up ((2 : int) * w2i n) <
         wr1_ipow wr1_radix (w2i n) * vm
       ==> wr1_value rp2 (w2i n) < (2 : int) * vm))`;

val wr1_all_sub_b_def = Define
  `wr1_all_sub_b
     (n:word32) (up: 'z wr1_ptr) (mp: 'z wr1_ptr) (rp1: 'z wr1_ptr)
     (rp2: 'z wr1_ptr) (o6:word64) (vm:int) <=>
     !b:word64. wr1_sub_b_body n up mp rp1 rp2 o6 vm b`;

val wr1_sub_rp2_body_def = Define
  `wr1_sub_rp2_body
     (n:word32) (up: 'z wr1_ptr) (mp: 'z wr1_ptr) (rp1: 'z wr1_ptr)
     (o6:word64) (vm:int) (rp2: 'z wr1_ptr) <=>
     wr1_same_metadata rp2 rp1
     ==> wr1_all_sub_b n up mp rp1 rp2 o6 vm`;

val wr1_all_sub_rp2_def = Define
  `wr1_all_sub_rp2
     (n:word32) (up: 'z wr1_ptr) (mp: 'z wr1_ptr) (rp1: 'z wr1_ptr)
     (o6:word64) (vm:int) <=>
     !rp2: 'z wr1_ptr. wr1_sub_rp2_body n up mp rp1 o6 vm rp2`;

val wr1_no_sub_result_def = Define
  `wr1_no_sub_result
     (n:word32) (up: 'z wr1_ptr) (rp1: 'z wr1_ptr) (o6:word64) (vm:int) <=>
     wr1_value rp1 (w2i n) % vm =
       (wr1_value rp1 (w2i n) +
        wr1_ipow wr1_radix (w2i n) * wr1_u64 o6) % vm /\
     (wr1_value up ((2 : int) * w2i n) <
        wr1_ipow wr1_radix (w2i n) * vm
      ==> wr1_value rp1 (w2i n) < (2 : int) * vm)`;

val wr1_o7_body_def = Define
  `wr1_o7_body
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (rp1: 'z wr1_ptr) (o6:word64) (vm:int) (o7:bool) <=>
     ((wr1_u64 o6 = (0 : int) ==> o7) /\
      (o7 ==> wr1_u64 o6 = (0 : int)))
     ==>
     ((if ~o7 then
         (0 : int) <= w2i n /\
         wr1_valid rp1 (w2i n) /\
         wr1_valid mp (w2i n) /\
         wr1_writable rp1 /\
         wr1_all_sub_rp2 n up mp rp1 o6 vm
       else wr1_no_sub_result n up rp1 o6 vm) /\
      wr1_all_final_rp2 n up rp mp rp1 o6 vm)`;

val wr1_all_o7_def = Define
  `wr1_all_o7
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (rp1: 'z wr1_ptr) (o6:word64) (vm:int) <=>
     !o7:bool. wr1_o7_body n up rp mp rp1 o6 vm o7`;

val wr1_o6_body_def = Define
  `wr1_o6_body
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (base: 'z wr1_ptr) (o5: 'z wr1_ptr) (rp1: 'z wr1_ptr) (vm:int) (o6:word64) <=>
     ((0 : int) <= wr1_u64 o6 /\ wr1_u64 o6 <= (1 : int) /\
      wr1_value rp1 (w2i n) +
        wr1_ipow wr1_radix (w2i n) * wr1_u64 o6 =
        wr1_value base (w2i n) + wr1_value o5 (w2i n) /\
      wr1_unchanged_outside rp1 rp (wr1_offset rp1) (w2i n))
     ==> wr1_all_o7 n up rp mp rp1 o6 vm`;

val wr1_all_o6_def = Define
  `wr1_all_o6
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (base: 'z wr1_ptr) (o5: 'z wr1_ptr) (rp1: 'z wr1_ptr) (vm:int) <=>
     !o6:word64. wr1_o6_body n up rp mp base o5 rp1 vm o6`;

val wr1_rp1_body_def = Define
  `wr1_rp1_body
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (base: 'z wr1_ptr) (o5: 'z wr1_ptr) (vm:int) (rp1: 'z wr1_ptr) <=>
     wr1_same_metadata rp1 rp
     ==> wr1_all_o6 n up rp mp base o5 rp1 vm`;

val wr1_all_rp1_def = Define
  `wr1_all_rp1
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (base: 'z wr1_ptr) (o5: 'z wr1_ptr) (vm:int) <=>
     !rp1: 'z wr1_ptr. wr1_rp1_body n up rp mp base o5 vm rp1`;

val wr1_final_o5_body_def = Define
  `wr1_final_o5_body
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (base: 'z wr1_ptr) (vm:int) (o4:word32) (o5: 'z wr1_ptr) <=>
     wr1_shift_state o5 base (w2i o4)
     ==>
     wr1_valid base (w2i n) /\
     wr1_valid o5 (w2i n) /\
     wr1_valid rp (w2i n) /\
     wr1_writable rp /\
     wr1_all_rp1 n up rp mp base o5 vm`;

val wr1_all_final_o5_def = Define
  `wr1_all_final_o5
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (base: 'z wr1_ptr) (vm:int) (o4:word32) <=>
     !o5: 'z wr1_ptr. wr1_final_o5_body n up rp mp base vm o4 o5`;

val wr1_negative_o4_body_def = Define
  `wr1_negative_o4_body
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (base: 'z wr1_ptr) (vm:int) (o4:word32) <=>
     w2i o4 = -(w2i n)
     ==>
     wr1_minimum base <= wr1_offset base + w2i o4 /\
     wr1_offset base + w2i o4 <= wr1_maximum base /\
     wr1_all_final_o5 n up rp mp base vm o4`;

val wr1_all_negative_o4_def = Define
  `wr1_all_negative_o4
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (base: 'z wr1_ptr) (vm:int) <=>
     !o4:word32. wr1_negative_o4_body n up rp mp base vm o4`;

val wr1_uprime_body_def = Define
  `wr1_uprime_body
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (base: 'z wr1_ptr) (vm:int) (o3:word32) (uprime: 'z wr1_ptr) <=>
     wr1_shift_state uprime base (w2i o3)
     ==>
     wr1_word32_in_bounds (-(w2i n)) /\
     wr1_all_negative_o4 n up rp mp base vm`;

val wr1_all_uprime_def = Define
  `wr1_all_uprime
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (base: 'z wr1_ptr) (vm:int) (o3:word32) <=>
     !uprime: 'z wr1_ptr. wr1_uprime_body n up rp mp base vm o3 uprime`;

val wr1_negative_o3_body_def = Define
  `wr1_negative_o3_body
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (base: 'z wr1_ptr) (vm:int) (o3:word32) <=>
     w2i o3 = -(w2i n)
     ==>
     wr1_minimum base <= wr1_offset base + w2i o3 /\
     wr1_offset base + w2i o3 <= wr1_maximum base /\
     wr1_all_uprime n up rp mp base vm o3`;

val wr1_all_negative_o3_def = Define
  `wr1_all_negative_o3
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (base: 'z wr1_ptr) (vm:int) <=>
     !o3:word32. wr1_negative_o3_body n up rp mp base vm o3`;

val wr1_final_stage_def = Define
  `wr1_final_stage
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (base: 'z wr1_ptr) (vm:int) <=>
     wr1_word32_in_bounds (-(w2i n)) /\
     wr1_all_negative_o3 n up rp mp base vm`;

val wr1_arithmetic_invariant_def = Define
  `wr1_arithmetic_invariant
     (n:word32) (up: 'z wr1_ptr) (vm:int) (added:int)
     (u: 'z wr1_ptr) (up1: 'z wr1_ptr) (index:int) <=>
     wr1_ipow wr1_radix index *
       wr1_value u ((w2i n + w2i n) - index) +
       wr1_ipow wr1_radix (w2i n) * wr1_value up1 index =
       wr1_value up (w2i n + w2i n) + vm * added /\
     (0 : int) <= added /\
     added < wr1_ipow wr1_radix index /\
     (wr1_ipow wr1_radix index *
        wr1_value u ((w2i n + w2i n) - index) +
        wr1_ipow wr1_radix (w2i n) * wr1_value up1 index) % vm =
       wr1_value up (w2i n + w2i n) % vm`;

val wr1_loop_invariant_def = Define
  `wr1_loop_invariant
     (n:word32) (up: 'z wr1_ptr) (o2:word32) (vm:int) (added:int)
     (u: 'z wr1_ptr) (up1: 'z wr1_ptr) (j:word32) <=>
     (0 : int) <= w2i j /\ w2i j <= w2i o2 /\
     wr1_offset u = wr1_offset up1 + w2i j /\
     wr1_same_pelts u up1 /\
     wr1_minimum u = wr1_minimum up1 /\
     wr1_maximum u = wr1_maximum up1 /\
     wr1_plength u = wr1_plength up1 /\
     wr1_writable u /\
     wr1_arithmetic_invariant n up vm added u up1 (w2i j)`;

val wr1_next_invariant_def = Define
  `wr1_next_invariant
     (n:word32) (up: 'z wr1_ptr) (vm:int) (added:int) (m:word64)
     (j:word32) (o5: 'z wr1_ptr) (up3: 'z wr1_ptr) <=>
     let next = w2i j + (1 : int) in
     let next_added =
       added + wr1_u64 m * wr1_ipow wr1_radix (w2i j) in
     wr1_offset o5 = wr1_offset up3 + next /\
     wr1_same_pelts o5 up3 /\
     wr1_minimum o5 = wr1_minimum up3 /\
     wr1_maximum o5 = wr1_maximum up3 /\
     wr1_plength o5 = wr1_plength up3 /\
     wr1_writable o5 /\
     wr1_arithmetic_invariant n up vm next_added o5 up3 next`;

val wr1_exit_invariant_def = Define
  `wr1_exit_invariant
     (n:word32) (up: 'z wr1_ptr) (o2:word32) (vm:int) (added:int)
     (u: 'z wr1_ptr) (up1: 'z wr1_ptr) <=>
     let index = w2i o2 + (1 : int) in
     wr1_offset u = wr1_offset up1 + index /\
     wr1_same_pelts u up1 /\
     wr1_minimum u = wr1_minimum up1 /\
     wr1_maximum u = wr1_maximum up1 /\
     wr1_plength u = wr1_plength up1 /\
     wr1_writable u /\
     wr1_arithmetic_invariant n up vm added u up1 index`;

val wr1_addmul_state_def = Define
  `wr1_addmul_state (u1: 'z wr1_ptr) (up2: 'z wr1_ptr) (u: 'z wr1_ptr) <=>
     wr1_data u1 = wr1_data up2 /\
     wr1_plength up2 = wr1_plength u /\
     wr1_offset u1 = wr1_offset u /\
     wr1_minimum u1 = wr1_minimum u /\
     wr1_maximum u1 = wr1_maximum u /\
     wr1_writable u1 = wr1_writable u /\
     wr1_zone u1 = wr1_zone u`;

val wr1_next_o5_body_def = Define
  `wr1_next_o5_body
     (n:word32) (up: 'z wr1_ptr) (vm:int) (added:int) (m:word64)
     (j:word32) (u2: 'z wr1_ptr) (up3: 'z wr1_ptr) (o5: 'z wr1_ptr) <=>
     wr1_shift_state o5 u2 (1 : int)
     ==> wr1_next_invariant n up vm added m j o5 up3`;

val wr1_all_next_o5_def = Define
  `wr1_all_next_o5
     (n:word32) (up: 'z wr1_ptr) (vm:int) (added:int) (m:word64)
     (j:word32) (u2: 'z wr1_ptr) (up3: 'z wr1_ptr) <=>
     !o5: 'z wr1_ptr. wr1_next_o5_body n up vm added m j u2 up3 o5`;

val wr1_u2_up3_body_def = Define
  `wr1_u2_up3_body
     (n:word32) (up: 'z wr1_ptr) (vm:int) (added:int) (m:word64)
     (j:word32) (u1: 'z wr1_ptr) (up2: 'z wr1_ptr) (u2: 'z wr1_ptr)
     (up3: 'z wr1_ptr) (o4:word64) <=>
     wr1_addmul_state u2 up3 u1
     ==> wr1_addmul_state u2 up3 u1
     ==> wr1_same_metadata up3 up2
     ==> wr1_updated_pelts u2 u1 (wr1_offset u2) o4
     ==> wr1_minimum u2 <= wr1_offset u2 + (1 : int) /\
         wr1_offset u2 + (1 : int) <= wr1_maximum u2 /\
         wr1_all_next_o5 n up vm added m j u2 up3`;

val wr1_all_u2_up3_def = Define
  `wr1_all_u2_up3
     (n:word32) (up: 'z wr1_ptr) (vm:int) (added:int) (m:word64)
     (j:word32) (u1: 'z wr1_ptr) (up2: 'z wr1_ptr) (o4:word64) <=>
     !u2: 'z wr1_ptr. !up3: 'z wr1_ptr.
       wr1_u2_up3_body n up vm added m j u1 up2 u2 up3 o4`;

val wr1_o4_body_def = Define
  `wr1_o4_body
     (n:word32) (up: 'z wr1_ptr) (mp: 'z wr1_ptr) (vm:int) (added:int)
     (u: 'z wr1_ptr) (m:word64) (j:word32) (u1: 'z wr1_ptr)
     (up2: 'z wr1_ptr) (o4:word64) <=>
     (wr1_value u1 (w2i n) +
        wr1_ipow wr1_radix (w2i n) * wr1_u64 o4 =
        wr1_value u (w2i n) + wr1_value mp (w2i n) * wr1_u64 m /\
      wr1_unchanged_outside u1 u (wr1_offset u1) (w2i n))
     ==>
     wr1_minimum u1 <= wr1_offset u1 /\
     wr1_offset u1 < wr1_maximum u1 /\
     wr1_writable u1 /\
     wr1_all_u2_up3 n up vm added m j u1 up2 o4`;

val wr1_all_o4_def = Define
  `wr1_all_o4
     (n:word32) (up: 'z wr1_ptr) (mp: 'z wr1_ptr) (vm:int) (added:int)
     (u: 'z wr1_ptr) (m:word64) (j:word32) (u1: 'z wr1_ptr) (up2: 'z wr1_ptr) <=>
     !o4:word64. wr1_o4_body n up mp vm added u m j u1 up2 o4`;

val wr1_u1_up2_body_def = Define
  `wr1_u1_up2_body
     (n:word32) (up: 'z wr1_ptr) (mp: 'z wr1_ptr) (vm:int) (added:int)
     (u: 'z wr1_ptr) (up1: 'z wr1_ptr) (m:word64) (j:word32)
     (u1: 'z wr1_ptr) (up2: 'z wr1_ptr) <=>
     wr1_addmul_state u1 up2 u
     ==> wr1_addmul_state u1 up2 u
     ==> wr1_same_metadata up2 up1
     ==> wr1_all_o4 n up mp vm added u m j u1 up2`;

val wr1_all_u1_up2_def = Define
  `wr1_all_u1_up2
     (n:word32) (up: 'z wr1_ptr) (mp: 'z wr1_ptr) (vm:int) (added:int)
     (u: 'z wr1_ptr) (up1: 'z wr1_ptr) (m:word64) (j:word32) <=>
     !u1: 'z wr1_ptr. !up2: 'z wr1_ptr.
       wr1_u1_up2_body n up mp vm added u up1 m j u1 up2`;

val wr1_nnj_body_def = Define
  `wr1_nnj_body
     (n:word32) (up: 'z wr1_ptr) (mp: 'z wr1_ptr) (vm:int) (added:int)
     (u: 'z wr1_ptr) (up1: 'z wr1_ptr) (m:word64) (j:word32)
     (o3:word32) (nnj:word32) <=>
     w2i nnj = w2i o3 - w2i j
     ==>
     wr1_valid mp (w2i n) /\
     wr1_valid u (w2i n) /\
     wr1_writable u /\
     wr1_all_u1_up2 n up mp vm added u up1 m j`;

val wr1_all_nnj_def = Define
  `wr1_all_nnj
     (n:word32) (up: 'z wr1_ptr) (mp: 'z wr1_ptr) (vm:int) (added:int)
     (u: 'z wr1_ptr) (up1: 'z wr1_ptr) (m:word64) (j:word32) (o3:word32) <=>
     !nnj:word32. wr1_nnj_body n up mp vm added u up1 m j o3 nnj`;

val wr1_positive_o3_body_def = Define
  `wr1_positive_o3_body
     (n:word32) (up: 'z wr1_ptr) (mp: 'z wr1_ptr) (vm:int) (added:int)
     (u: 'z wr1_ptr) (up1: 'z wr1_ptr) (m:word64) (j:word32) (o3:word32) <=>
     w2i o3 = w2i n + w2i n
     ==>
     wr1_word32_in_bounds (w2i o3 - w2i j) /\
     wr1_all_nnj n up mp vm added u up1 m j o3`;

val wr1_all_positive_o3_def = Define
  `wr1_all_positive_o3
     (n:word32) (up: 'z wr1_ptr) (mp: 'z wr1_ptr) (vm:int) (added:int)
     (u: 'z wr1_ptr) (up1: 'z wr1_ptr) (m:word64) (j:word32) <=>
     !o3:word32.
       wr1_positive_o3_body n up mp vm added u up1 m j o3`;

val wr1_m_body_def = Define
  `wr1_m_body
     (n:word32) (up: 'z wr1_ptr) (mp: 'z wr1_ptr) (invm:word64) (vm:int)
     (added:int) (u: 'z wr1_ptr) (up1: 'z wr1_ptr) (j:word32) (m:word64) <=>
     wr1_u64 m =
       (wr1_u64 (wr1_pelt u (wr1_offset u)) * wr1_u64 invm)
       % wr1_radix
     ==>
     wr1_word32_in_bounds (w2i n + w2i n) /\
     wr1_all_positive_o3 n up mp vm added u up1 m j`;

val wr1_all_m_def = Define
  `wr1_all_m
     (n:word32) (up: 'z wr1_ptr) (mp: 'z wr1_ptr) (invm:word64) (vm:int)
     (added:int) (u: 'z wr1_ptr) (up1: 'z wr1_ptr) (j:word32) <=>
     !m:word64. wr1_m_body n up mp invm vm added u up1 j m`;

val wr1_j_body_def = Define
  `wr1_j_body
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (invm:word64) (o2:word32) (vm:int) (added:int)
     (u: 'z wr1_ptr) (up1: 'z wr1_ptr) (j:word32) <=>
     (wr1_loop_invariant n up o2 vm added u up1 j
      ==>
      wr1_minimum u <= wr1_offset u /\
      wr1_offset u < wr1_maximum u /\
      wr1_all_m n up mp invm vm added u up1 j) /\
     (wr1_exit_invariant n up o2 vm added u up1
      ==> wr1_final_stage n up rp mp u vm)`;

val wr1_all_j_def = Define
  `wr1_all_j
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (invm:word64) (o2:word32) (vm:int) (added:int)
     (u: 'z wr1_ptr) (up1: 'z wr1_ptr) <=>
     !j:word32. wr1_j_body n up rp mp invm o2 vm added u up1 j`;

val wr1_loop_state_body_def = Define
  `wr1_loop_state_body
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (invm:word64) (o2:word32) (vm:int) (added:int)
     (u: 'z wr1_ptr) (up1: 'z wr1_ptr) <=>
     wr1_same_metadata up1 up
     ==> wr1_all_j n up rp mp invm o2 vm added u up1`;

val wr1_all_loop_states_def = Define
  `wr1_all_loop_states
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (invm:word64) (o2:word32) (vm:int) <=>
     !added:int. !u: 'z wr1_ptr. !up1: 'z wr1_ptr.
       wr1_loop_state_body n up rp mp invm o2 vm added u up1`;

val wr1_initial_invariant_def = Define
  `wr1_initial_invariant
     (n:word32) (up: 'z wr1_ptr) (o1: 'z wr1_ptr) (vm:int) <=>
     wr1_offset o1 = wr1_offset up + (0 : int) /\
     wr1_same_pelts o1 up /\
     wr1_minimum o1 = wr1_minimum up /\
     wr1_maximum o1 = wr1_maximum up /\
     wr1_plength o1 = wr1_plength up /\
     wr1_writable o1 /\
     wr1_ipow wr1_radix (0 : int) *
       wr1_value o1 ((w2i n + w2i n) - (0 : int)) +
       wr1_ipow wr1_radix (w2i n) * wr1_value up (0 : int) =
       wr1_value up (w2i n + w2i n) + vm * (0 : int) /\
     (0 : int) <= (0 : int) /\
     (0 : int) < wr1_ipow wr1_radix (0 : int) /\
     (wr1_ipow wr1_radix (0 : int) *
        wr1_value o1 ((w2i n + w2i n) - (0 : int)) +
        wr1_ipow wr1_radix (w2i n) * wr1_value up (0 : int)) % vm =
       wr1_value up (w2i n + w2i n) % vm`;

val wr1_o2_body_def = Define
  `wr1_o2_body
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (invm:word64) (o1: 'z wr1_ptr) (vm:int) (o2:word32) <=>
     w2i o2 = w2i n - (1 : int)
     ==>
     ((0 : int) <= w2i o2 + (1 : int)
      ==> wr1_initial_invariant n up o1 vm /\
          wr1_all_loop_states n up rp mp invm o2 vm) /\
     (w2i o2 + (1 : int) < (0 : int)
      ==> wr1_final_stage n up rp mp o1 vm)`;

val wr1_all_o2_def = Define
  `wr1_all_o2
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (invm:word64) (o1: 'z wr1_ptr) (vm:int) <=>
     !o2:word32. wr1_o2_body n up rp mp invm o1 vm o2`;

val wr1_o1_body_def = Define
  `wr1_o1_body
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (invm:word64) (o1: 'z wr1_ptr) <=>
     wr1_shift_state o1 up (0 : int)
     ==>
     let vm = wr1_value mp (w2i n) in
     wr1_word32_in_bounds (w2i n - (1 : int)) /\
     wr1_all_o2 n up rp mp invm o1 vm`;

val wr1_all_o1_def = Define
  `wr1_all_o1
     (n:word32) (up: 'z wr1_ptr) (rp: 'z wr1_ptr) (mp: 'z wr1_ptr)
     (invm:word64) <=>
     !o1: 'z wr1_ptr. wr1_o1_body n up rp mp invm o1`;

val powm_Powm_wmpn_redc_1qtvc_statement =
  ``!n:word32. !mp: 'z wr1_ptr. !up: 'z wr1_ptr. !rp: 'z wr1_ptr. !invm:word64.
     ((0 : int) < w2i n /\
      wr1_valid mp (w2i n) /\
      wr1_valid up ((2 : int) * w2i n) /\
      wr1_valid rp (w2i n) /\
      ODD (wr1_to_num (wr1_value mp (w2i n))) /\
      (wr1_value mp (w2i n) * wr1_u64 invm) % wr1_radix =
        wr1_radix - (1 : int) /\
      wr1_writable up /\
      wr1_writable rp)
     ==>
     wr1_minimum up <= wr1_offset up + (0 : int) /\
     wr1_offset up + (0 : int) <= wr1_maximum up /\
     wr1_all_o1 n up rp mp invm``;

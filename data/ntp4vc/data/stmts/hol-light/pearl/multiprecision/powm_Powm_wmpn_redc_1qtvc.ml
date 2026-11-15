(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/powm_Powm_wmpn_redc_1qtvc: the verification condition
  for one-limb Montgomery reduction of a double-width multiprecision integer,
  including its loop invariant and final conditional subtraction. This file
  contains no proof.
*)

needs "Library/words.ml";;
needs "Library/isum.ml";;

new_type_abbrev
  ("wr1_ptr",`:(int64 list)#(int#(int#(int#(bool#'z))))`);;

let wr1_radix = new_definition
  `wr1_radix = (&18446744073709551616:int)`;;

let wr1_u64 = new_definition
  `wr1_u64 (x:int64) = (&(val x):int)`;;

let wr1_int32_in_bounds = new_definition
  `wr1_int32_in_bounds (x:int) <=>
     --(&2147483648:int) <= x /\ x <= (&2147483647:int)`;;

let wr1_ipow = new_definition
  `wr1_ipow (base:int) (exponent:int) =
     base pow (num_of_int exponent)`;;

let wr1_data = new_definition
  `wr1_data (p:wr1_ptr) = FST p`;;

let wr1_offset = new_definition
  `wr1_offset (p:wr1_ptr) = FST (SND p)`;;

let wr1_minimum = new_definition
  `wr1_minimum (p:wr1_ptr) = FST (SND (SND p))`;;

let wr1_maximum = new_definition
  `wr1_maximum (p:wr1_ptr) = FST (SND (SND (SND p)))`;;

let wr1_writable = new_definition
  `wr1_writable (p:wr1_ptr) = FST (SND (SND (SND (SND p))))`;;

let wr1_zone = new_definition
  `wr1_zone (p:wr1_ptr) = SND (SND (SND (SND (SND p))))`;;

let wr1_pelt = new_definition
  `wr1_pelt (p:wr1_ptr) (i:int) =
     if i < (&0:int) then (word 0:int64)
     else if num_of_int i < LENGTH (wr1_data p)
          then EL (num_of_int i) (wr1_data p)
          else (word 0:int64)`;;

let wr1_plength = new_definition
  `wr1_plength (p:wr1_ptr) = (&(LENGTH (wr1_data p)):int)`;;

let wr1_valid = new_definition
  `wr1_valid (p:wr1_ptr) (size:int) <=>
     wr1_int32_in_bounds size /\
     (&0:int) <= size /\
     (&0:int) <= wr1_minimum p /\
     wr1_minimum p <= wr1_offset p /\
     wr1_offset p + size <= wr1_maximum p /\
     wr1_maximum p <= wr1_plength p`;;

let wr1_value = new_definition
  `wr1_value (p:wr1_ptr) (size:int) =
     if size <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int size - 1)
         (\k. wr1_ipow wr1_radix (&k) *
              wr1_u64 (wr1_pelt p (wr1_offset p + &k)))`;;

let wr1_redc = new_definition
  `wr1_redc (ur:int) (u:int) (n:int) (modulus:int) <=>
     ur rem modulus =
     (wr1_ipow wr1_radix n * u) rem modulus`;;

let wr1_same_pelts = new_definition
  `wr1_same_pelts (left:wr1_ptr) (right:wr1_ptr) <=>
     !index:int. wr1_pelt left index = wr1_pelt right index`;;

let wr1_same_metadata = new_definition
  `wr1_same_metadata (left:wr1_ptr) (right:wr1_ptr) <=>
     wr1_plength left = wr1_plength right /\
     wr1_offset left = wr1_offset right /\
     wr1_minimum left = wr1_minimum right /\
     wr1_maximum left = wr1_maximum right /\
     wr1_writable left = wr1_writable right /\
     wr1_zone left = wr1_zone right`;;

let wr1_shift_state = new_definition
  `wr1_shift_state (newp:wr1_ptr) (oldp:wr1_ptr) (amount:int) <=>
     wr1_offset newp = wr1_offset oldp + amount /\
     wr1_plength newp = wr1_plength oldp /\
     wr1_same_pelts newp oldp /\
     wr1_data newp = wr1_data oldp /\
     wr1_minimum newp = wr1_minimum oldp /\
     wr1_maximum newp = wr1_maximum oldp /\
     wr1_zone newp = wr1_zone oldp /\
     wr1_writable newp = wr1_writable oldp`;;

let wr1_unchanged_outside = new_definition
  `wr1_unchanged_outside
     (newp:wr1_ptr) (oldp:wr1_ptr) (start:int) (size:int) <=>
     !index:int.
       index < start \/ start + size <= index
       ==> wr1_pelt newp index = wr1_pelt oldp index`;;

let wr1_updated_pelts = new_definition
  `wr1_updated_pelts
     (newp:wr1_ptr) (oldp:wr1_ptr) (update_index:int)
     (update_value:int64) <=>
     !index:int.
       wr1_pelt newp index =
       if index = update_index then update_value else wr1_pelt oldp index`;;

let wr1_final_rp2_premise = new_definition
  `wr1_final_rp2_premise
     (n:int32) (up:wr1_ptr) (rp1:wr1_ptr) (rp2:wr1_ptr)
     (o6:int64) (vm:int) <=>
     wr1_value rp2 (ival n) rem vm =
       (wr1_value rp1 (ival n) +
        wr1_ipow wr1_radix (ival n) * wr1_u64 o6) rem vm /\
     wr1_unchanged_outside rp2 rp1 (wr1_offset rp2) (ival n) /\
     (wr1_value up ((&2:int) * ival n) <
        wr1_ipow wr1_radix (ival n) * vm
      ==> wr1_value rp2 (ival n) < (&2:int) * vm)`;;

let wr1_final_rp2_conclusion = new_definition
  `wr1_final_rp2_conclusion
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr) (rp2:wr1_ptr) <=>
     wr1_redc
       (wr1_value up ((&2:int) * ival n))
       (wr1_value rp2 (ival n))
       (ival n)
       (wr1_value mp (ival n)) /\
     wr1_unchanged_outside rp2 rp (wr1_offset rp2) (ival n) /\
     (wr1_value up ((&2:int) * ival n) <
        wr1_ipow wr1_radix (ival n) * wr1_value mp (ival n)
      ==> wr1_value rp2 (ival n) <
          (&2:int) * wr1_value mp (ival n))`;;

let wr1_final_rp2_body = new_definition
  `wr1_final_rp2_body
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (rp1:wr1_ptr) (o6:int64) (vm:int) (rp2:wr1_ptr) <=>
     wr1_same_metadata rp2 rp1
     ==> wr1_final_rp2_premise n up rp1 rp2 o6 vm
     ==> wr1_final_rp2_conclusion n up rp mp rp2`;;

let wr1_all_final_rp2 = new_definition
  `wr1_all_final_rp2
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (rp1:wr1_ptr) (o6:int64) (vm:int) <=>
     !rp2:wr1_ptr. wr1_final_rp2_body n up rp mp rp1 o6 vm rp2`;;

let wr1_sub_b_body = new_definition
  `wr1_sub_b_body
     (n:int32) (up:wr1_ptr) (mp:wr1_ptr) (rp1:wr1_ptr)
     (rp2:wr1_ptr) (o6:int64) (vm:int) (b:int64) <=>
     (wr1_value rp2 (ival n) -
        wr1_ipow wr1_radix (ival n) * wr1_u64 b =
        wr1_value rp1 (ival n) - wr1_value mp (ival n) /\
      (&0:int) <= wr1_u64 b /\ wr1_u64 b <= (&1:int) /\
      wr1_unchanged_outside rp2 rp1 (wr1_offset rp2) (ival n))
     ==>
     (wr1_value rp2 (ival n) rem vm =
        (wr1_value rp1 (ival n) +
         wr1_ipow wr1_radix (ival n) * wr1_u64 o6) rem vm /\
      wr1_unchanged_outside rp2 rp1 (wr1_offset rp2) (ival n) /\
      (wr1_value up ((&2:int) * ival n) <
         wr1_ipow wr1_radix (ival n) * vm
       ==> wr1_value rp2 (ival n) < (&2:int) * vm))`;;

let wr1_all_sub_b = new_definition
  `wr1_all_sub_b
     (n:int32) (up:wr1_ptr) (mp:wr1_ptr) (rp1:wr1_ptr)
     (rp2:wr1_ptr) (o6:int64) (vm:int) <=>
     !b:int64. wr1_sub_b_body n up mp rp1 rp2 o6 vm b`;;

let wr1_sub_rp2_body = new_definition
  `wr1_sub_rp2_body
     (n:int32) (up:wr1_ptr) (mp:wr1_ptr) (rp1:wr1_ptr)
     (o6:int64) (vm:int) (rp2:wr1_ptr) <=>
     wr1_same_metadata rp2 rp1
     ==> wr1_all_sub_b n up mp rp1 rp2 o6 vm`;;

let wr1_all_sub_rp2 = new_definition
  `wr1_all_sub_rp2
     (n:int32) (up:wr1_ptr) (mp:wr1_ptr) (rp1:wr1_ptr)
     (o6:int64) (vm:int) <=>
     !rp2:wr1_ptr. wr1_sub_rp2_body n up mp rp1 o6 vm rp2`;;

let wr1_no_sub_result = new_definition
  `wr1_no_sub_result
     (n:int32) (up:wr1_ptr) (rp1:wr1_ptr) (o6:int64) (vm:int) <=>
     wr1_value rp1 (ival n) rem vm =
       (wr1_value rp1 (ival n) +
        wr1_ipow wr1_radix (ival n) * wr1_u64 o6) rem vm /\
     (wr1_value up ((&2:int) * ival n) <
        wr1_ipow wr1_radix (ival n) * vm
      ==> wr1_value rp1 (ival n) < (&2:int) * vm)`;;

let wr1_o7_body = new_definition
  `wr1_o7_body
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (rp1:wr1_ptr) (o6:int64) (vm:int) (o7:bool) <=>
     ((wr1_u64 o6 = (&0:int) ==> o7) /\
      (o7 ==> wr1_u64 o6 = (&0:int)))
     ==>
     ((if ~o7 then
         (&0:int) <= ival n /\
         wr1_valid rp1 (ival n) /\
         wr1_valid mp (ival n) /\
         wr1_writable rp1 /\
         wr1_all_sub_rp2 n up mp rp1 o6 vm
       else wr1_no_sub_result n up rp1 o6 vm) /\
      wr1_all_final_rp2 n up rp mp rp1 o6 vm)`;;

let wr1_all_o7 = new_definition
  `wr1_all_o7
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (rp1:wr1_ptr) (o6:int64) (vm:int) <=>
     !o7:bool. wr1_o7_body n up rp mp rp1 o6 vm o7`;;

let wr1_o6_body = new_definition
  `wr1_o6_body
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (base:wr1_ptr) (o5:wr1_ptr) (rp1:wr1_ptr) (vm:int) (o6:int64) <=>
     ((&0:int) <= wr1_u64 o6 /\ wr1_u64 o6 <= (&1:int) /\
      wr1_value rp1 (ival n) +
        wr1_ipow wr1_radix (ival n) * wr1_u64 o6 =
        wr1_value base (ival n) + wr1_value o5 (ival n) /\
      wr1_unchanged_outside rp1 rp (wr1_offset rp1) (ival n))
     ==> wr1_all_o7 n up rp mp rp1 o6 vm`;;

let wr1_all_o6 = new_definition
  `wr1_all_o6
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (base:wr1_ptr) (o5:wr1_ptr) (rp1:wr1_ptr) (vm:int) <=>
     !o6:int64. wr1_o6_body n up rp mp base o5 rp1 vm o6`;;

let wr1_rp1_body = new_definition
  `wr1_rp1_body
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (base:wr1_ptr) (o5:wr1_ptr) (vm:int) (rp1:wr1_ptr) <=>
     wr1_same_metadata rp1 rp
     ==> wr1_all_o6 n up rp mp base o5 rp1 vm`;;

let wr1_all_rp1 = new_definition
  `wr1_all_rp1
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (base:wr1_ptr) (o5:wr1_ptr) (vm:int) <=>
     !rp1:wr1_ptr. wr1_rp1_body n up rp mp base o5 vm rp1`;;

let wr1_final_o5_body = new_definition
  `wr1_final_o5_body
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (base:wr1_ptr) (vm:int) (o4:int32) (o5:wr1_ptr) <=>
     wr1_shift_state o5 base (ival o4)
     ==>
     wr1_valid base (ival n) /\
     wr1_valid o5 (ival n) /\
     wr1_valid rp (ival n) /\
     wr1_writable rp /\
     wr1_all_rp1 n up rp mp base o5 vm`;;

let wr1_all_final_o5 = new_definition
  `wr1_all_final_o5
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (base:wr1_ptr) (vm:int) (o4:int32) <=>
     !o5:wr1_ptr. wr1_final_o5_body n up rp mp base vm o4 o5`;;

let wr1_negative_o4_body = new_definition
  `wr1_negative_o4_body
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (base:wr1_ptr) (vm:int) (o4:int32) <=>
     ival o4 = --(ival n)
     ==>
     wr1_minimum base <= wr1_offset base + ival o4 /\
     wr1_offset base + ival o4 <= wr1_maximum base /\
     wr1_all_final_o5 n up rp mp base vm o4`;;

let wr1_all_negative_o4 = new_definition
  `wr1_all_negative_o4
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (base:wr1_ptr) (vm:int) <=>
     !o4:int32. wr1_negative_o4_body n up rp mp base vm o4`;;

let wr1_uprime_body = new_definition
  `wr1_uprime_body
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (base:wr1_ptr) (vm:int) (o3:int32) (uprime:wr1_ptr) <=>
     wr1_shift_state uprime base (ival o3)
     ==>
     wr1_int32_in_bounds (--(ival n)) /\
     wr1_all_negative_o4 n up rp mp base vm`;;

let wr1_all_uprime = new_definition
  `wr1_all_uprime
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (base:wr1_ptr) (vm:int) (o3:int32) <=>
     !uprime:wr1_ptr. wr1_uprime_body n up rp mp base vm o3 uprime`;;

let wr1_negative_o3_body = new_definition
  `wr1_negative_o3_body
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (base:wr1_ptr) (vm:int) (o3:int32) <=>
     ival o3 = --(ival n)
     ==>
     wr1_minimum base <= wr1_offset base + ival o3 /\
     wr1_offset base + ival o3 <= wr1_maximum base /\
     wr1_all_uprime n up rp mp base vm o3`;;

let wr1_all_negative_o3 = new_definition
  `wr1_all_negative_o3
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (base:wr1_ptr) (vm:int) <=>
     !o3:int32. wr1_negative_o3_body n up rp mp base vm o3`;;

let wr1_final_stage = new_definition
  `wr1_final_stage
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (base:wr1_ptr) (vm:int) <=>
     wr1_int32_in_bounds (--(ival n)) /\
     wr1_all_negative_o3 n up rp mp base vm`;;

let wr1_arithmetic_invariant = new_definition
  `wr1_arithmetic_invariant
     (n:int32) (up:wr1_ptr) (vm:int) (added:int)
     (u:wr1_ptr) (up1:wr1_ptr) (index:int) <=>
     wr1_ipow wr1_radix index *
       wr1_value u ((ival n + ival n) - index) +
       wr1_ipow wr1_radix (ival n) * wr1_value up1 index =
       wr1_value up (ival n + ival n) + vm * added /\
     (&0:int) <= added /\
     added < wr1_ipow wr1_radix index /\
     (wr1_ipow wr1_radix index *
        wr1_value u ((ival n + ival n) - index) +
        wr1_ipow wr1_radix (ival n) * wr1_value up1 index) rem vm =
       wr1_value up (ival n + ival n) rem vm`;;

let wr1_loop_invariant = new_definition
  `wr1_loop_invariant
     (n:int32) (up:wr1_ptr) (o2:int32) (vm:int) (added:int)
     (u:wr1_ptr) (up1:wr1_ptr) (j:int32) <=>
     (&0:int) <= ival j /\ ival j <= ival o2 /\
     wr1_offset u = wr1_offset up1 + ival j /\
     wr1_same_pelts u up1 /\
     wr1_minimum u = wr1_minimum up1 /\
     wr1_maximum u = wr1_maximum up1 /\
     wr1_plength u = wr1_plength up1 /\
     wr1_writable u /\
     wr1_arithmetic_invariant n up vm added u up1 (ival j)`;;

let wr1_next_invariant = new_definition
  `wr1_next_invariant
     (n:int32) (up:wr1_ptr) (vm:int) (added:int) (m:int64)
     (j:int32) (o5:wr1_ptr) (up3:wr1_ptr) <=>
     let next = ival j + (&1:int) in
     let next_added =
       added + wr1_u64 m * wr1_ipow wr1_radix (ival j) in
     wr1_offset o5 = wr1_offset up3 + next /\
     wr1_same_pelts o5 up3 /\
     wr1_minimum o5 = wr1_minimum up3 /\
     wr1_maximum o5 = wr1_maximum up3 /\
     wr1_plength o5 = wr1_plength up3 /\
     wr1_writable o5 /\
     wr1_arithmetic_invariant n up vm next_added o5 up3 next`;;

let wr1_exit_invariant = new_definition
  `wr1_exit_invariant
     (n:int32) (up:wr1_ptr) (o2:int32) (vm:int) (added:int)
     (u:wr1_ptr) (up1:wr1_ptr) <=>
     let index = ival o2 + (&1:int) in
     wr1_offset u = wr1_offset up1 + index /\
     wr1_same_pelts u up1 /\
     wr1_minimum u = wr1_minimum up1 /\
     wr1_maximum u = wr1_maximum up1 /\
     wr1_plength u = wr1_plength up1 /\
     wr1_writable u /\
     wr1_arithmetic_invariant n up vm added u up1 index`;;

let wr1_addmul_state = new_definition
  `wr1_addmul_state (u1:wr1_ptr) (up2:wr1_ptr) (u:wr1_ptr) <=>
     wr1_data u1 = wr1_data up2 /\
     wr1_plength up2 = wr1_plength u /\
     wr1_offset u1 = wr1_offset u /\
     wr1_minimum u1 = wr1_minimum u /\
     wr1_maximum u1 = wr1_maximum u /\
     wr1_writable u1 = wr1_writable u /\
     wr1_zone u1 = wr1_zone u`;;

let wr1_next_o5_body = new_definition
  `wr1_next_o5_body
     (n:int32) (up:wr1_ptr) (vm:int) (added:int) (m:int64)
     (j:int32) (u2:wr1_ptr) (up3:wr1_ptr) (o5:wr1_ptr) <=>
     wr1_shift_state o5 u2 (&1:int)
     ==> wr1_next_invariant n up vm added m j o5 up3`;;

let wr1_all_next_o5 = new_definition
  `wr1_all_next_o5
     (n:int32) (up:wr1_ptr) (vm:int) (added:int) (m:int64)
     (j:int32) (u2:wr1_ptr) (up3:wr1_ptr) <=>
     !o5:wr1_ptr. wr1_next_o5_body n up vm added m j u2 up3 o5`;;

let wr1_u2_up3_body = new_definition
  `wr1_u2_up3_body
     (n:int32) (up:wr1_ptr) (vm:int) (added:int) (m:int64)
     (j:int32) (u1:wr1_ptr) (up2:wr1_ptr) (u2:wr1_ptr)
     (up3:wr1_ptr) (o4:int64) <=>
     wr1_addmul_state u2 up3 u1
     ==> wr1_addmul_state u2 up3 u1
     ==> wr1_same_metadata up3 up2
     ==> wr1_updated_pelts u2 u1 (wr1_offset u2) o4
     ==> wr1_minimum u2 <= wr1_offset u2 + (&1:int) /\
         wr1_offset u2 + (&1:int) <= wr1_maximum u2 /\
         wr1_all_next_o5 n up vm added m j u2 up3`;;

let wr1_all_u2_up3 = new_definition
  `wr1_all_u2_up3
     (n:int32) (up:wr1_ptr) (vm:int) (added:int) (m:int64)
     (j:int32) (u1:wr1_ptr) (up2:wr1_ptr) (o4:int64) <=>
     !u2:wr1_ptr. !up3:wr1_ptr.
       wr1_u2_up3_body n up vm added m j u1 up2 u2 up3 o4`;;

let wr1_o4_body = new_definition
  `wr1_o4_body
     (n:int32) (up:wr1_ptr) (mp:wr1_ptr) (vm:int) (added:int)
     (u:wr1_ptr) (m:int64) (j:int32) (u1:wr1_ptr)
     (up2:wr1_ptr) (o4:int64) <=>
     (wr1_value u1 (ival n) +
        wr1_ipow wr1_radix (ival n) * wr1_u64 o4 =
        wr1_value u (ival n) + wr1_value mp (ival n) * wr1_u64 m /\
      wr1_unchanged_outside u1 u (wr1_offset u1) (ival n))
     ==>
     wr1_minimum u1 <= wr1_offset u1 /\
     wr1_offset u1 < wr1_maximum u1 /\
     wr1_writable u1 /\
     wr1_all_u2_up3 n up vm added m j u1 up2 o4`;;

let wr1_all_o4 = new_definition
  `wr1_all_o4
     (n:int32) (up:wr1_ptr) (mp:wr1_ptr) (vm:int) (added:int)
     (u:wr1_ptr) (m:int64) (j:int32) (u1:wr1_ptr) (up2:wr1_ptr) <=>
     !o4:int64. wr1_o4_body n up mp vm added u m j u1 up2 o4`;;

let wr1_u1_up2_body = new_definition
  `wr1_u1_up2_body
     (n:int32) (up:wr1_ptr) (mp:wr1_ptr) (vm:int) (added:int)
     (u:wr1_ptr) (up1:wr1_ptr) (m:int64) (j:int32)
     (u1:wr1_ptr) (up2:wr1_ptr) <=>
     wr1_addmul_state u1 up2 u
     ==> wr1_addmul_state u1 up2 u
     ==> wr1_same_metadata up2 up1
     ==> wr1_all_o4 n up mp vm added u m j u1 up2`;;

let wr1_all_u1_up2 = new_definition
  `wr1_all_u1_up2
     (n:int32) (up:wr1_ptr) (mp:wr1_ptr) (vm:int) (added:int)
     (u:wr1_ptr) (up1:wr1_ptr) (m:int64) (j:int32) <=>
     !u1:wr1_ptr. !up2:wr1_ptr.
       wr1_u1_up2_body n up mp vm added u up1 m j u1 up2`;;

let wr1_nnj_body = new_definition
  `wr1_nnj_body
     (n:int32) (up:wr1_ptr) (mp:wr1_ptr) (vm:int) (added:int)
     (u:wr1_ptr) (up1:wr1_ptr) (m:int64) (j:int32)
     (o3:int32) (nnj:int32) <=>
     ival nnj = ival o3 - ival j
     ==>
     wr1_valid mp (ival n) /\
     wr1_valid u (ival n) /\
     wr1_writable u /\
     wr1_all_u1_up2 n up mp vm added u up1 m j`;;

let wr1_all_nnj = new_definition
  `wr1_all_nnj
     (n:int32) (up:wr1_ptr) (mp:wr1_ptr) (vm:int) (added:int)
     (u:wr1_ptr) (up1:wr1_ptr) (m:int64) (j:int32) (o3:int32) <=>
     !nnj:int32. wr1_nnj_body n up mp vm added u up1 m j o3 nnj`;;

let wr1_positive_o3_body = new_definition
  `wr1_positive_o3_body
     (n:int32) (up:wr1_ptr) (mp:wr1_ptr) (vm:int) (added:int)
     (u:wr1_ptr) (up1:wr1_ptr) (m:int64) (j:int32) (o3:int32) <=>
     ival o3 = ival n + ival n
     ==>
     wr1_int32_in_bounds (ival o3 - ival j) /\
     wr1_all_nnj n up mp vm added u up1 m j o3`;;

let wr1_all_positive_o3 = new_definition
  `wr1_all_positive_o3
     (n:int32) (up:wr1_ptr) (mp:wr1_ptr) (vm:int) (added:int)
     (u:wr1_ptr) (up1:wr1_ptr) (m:int64) (j:int32) <=>
     !o3:int32.
       wr1_positive_o3_body n up mp vm added u up1 m j o3`;;

let wr1_m_body = new_definition
  `wr1_m_body
     (n:int32) (up:wr1_ptr) (mp:wr1_ptr) (invm:int64) (vm:int)
     (added:int) (u:wr1_ptr) (up1:wr1_ptr) (j:int32) (m:int64) <=>
     wr1_u64 m =
       (wr1_u64 (wr1_pelt u (wr1_offset u)) * wr1_u64 invm)
       rem wr1_radix
     ==>
     wr1_int32_in_bounds (ival n + ival n) /\
     wr1_all_positive_o3 n up mp vm added u up1 m j`;;

let wr1_all_m = new_definition
  `wr1_all_m
     (n:int32) (up:wr1_ptr) (mp:wr1_ptr) (invm:int64) (vm:int)
     (added:int) (u:wr1_ptr) (up1:wr1_ptr) (j:int32) <=>
     !m:int64. wr1_m_body n up mp invm vm added u up1 j m`;;

let wr1_j_body = new_definition
  `wr1_j_body
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (invm:int64) (o2:int32) (vm:int) (added:int)
     (u:wr1_ptr) (up1:wr1_ptr) (j:int32) <=>
     (wr1_loop_invariant n up o2 vm added u up1 j
      ==>
      wr1_minimum u <= wr1_offset u /\
      wr1_offset u < wr1_maximum u /\
      wr1_all_m n up mp invm vm added u up1 j) /\
     (wr1_exit_invariant n up o2 vm added u up1
      ==> wr1_final_stage n up rp mp u vm)`;;

let wr1_all_j = new_definition
  `wr1_all_j
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (invm:int64) (o2:int32) (vm:int) (added:int)
     (u:wr1_ptr) (up1:wr1_ptr) <=>
     !j:int32. wr1_j_body n up rp mp invm o2 vm added u up1 j`;;

let wr1_loop_state_body = new_definition
  `wr1_loop_state_body
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (invm:int64) (o2:int32) (vm:int) (added:int)
     (u:wr1_ptr) (up1:wr1_ptr) <=>
     wr1_same_metadata up1 up
     ==> wr1_all_j n up rp mp invm o2 vm added u up1`;;

let wr1_all_loop_states = new_definition
  `wr1_all_loop_states
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (invm:int64) (o2:int32) (vm:int) <=>
     !added:int. !u:wr1_ptr. !up1:wr1_ptr.
       wr1_loop_state_body n up rp mp invm o2 vm added u up1`;;

let wr1_initial_invariant = new_definition
  `wr1_initial_invariant
     (n:int32) (up:wr1_ptr) (o1:wr1_ptr) (vm:int) <=>
     wr1_offset o1 = wr1_offset up + (&0:int) /\
     wr1_same_pelts o1 up /\
     wr1_minimum o1 = wr1_minimum up /\
     wr1_maximum o1 = wr1_maximum up /\
     wr1_plength o1 = wr1_plength up /\
     wr1_writable o1 /\
     wr1_ipow wr1_radix (&0:int) *
       wr1_value o1 ((ival n + ival n) - (&0:int)) +
       wr1_ipow wr1_radix (ival n) * wr1_value up (&0:int) =
       wr1_value up (ival n + ival n) + vm * (&0:int) /\
     (&0:int) <= (&0:int) /\
     (&0:int) < wr1_ipow wr1_radix (&0:int) /\
     (wr1_ipow wr1_radix (&0:int) *
        wr1_value o1 ((ival n + ival n) - (&0:int)) +
        wr1_ipow wr1_radix (ival n) * wr1_value up (&0:int)) rem vm =
       wr1_value up (ival n + ival n) rem vm`;;

let wr1_o2_body = new_definition
  `wr1_o2_body
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (invm:int64) (o1:wr1_ptr) (vm:int) (o2:int32) <=>
     ival o2 = ival n - (&1:int)
     ==>
     ((&0:int) <= ival o2 + (&1:int)
      ==> wr1_initial_invariant n up o1 vm /\
          wr1_all_loop_states n up rp mp invm o2 vm) /\
     (ival o2 + (&1:int) < (&0:int)
      ==> wr1_final_stage n up rp mp o1 vm)`;;

let wr1_all_o2 = new_definition
  `wr1_all_o2
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (invm:int64) (o1:wr1_ptr) (vm:int) <=>
     !o2:int32. wr1_o2_body n up rp mp invm o1 vm o2`;;

let wr1_o1_body = new_definition
  `wr1_o1_body
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (invm:int64) (o1:wr1_ptr) <=>
     wr1_shift_state o1 up (&0:int)
     ==>
     let vm = wr1_value mp (ival n) in
     wr1_int32_in_bounds (ival n - (&1:int)) /\
     wr1_all_o2 n up rp mp invm o1 vm`;;

let wr1_all_o1 = new_definition
  `wr1_all_o1
     (n:int32) (up:wr1_ptr) (rp:wr1_ptr) (mp:wr1_ptr)
     (invm:int64) <=>
     !o1:wr1_ptr. wr1_o1_body n up rp mp invm o1`;;

let statement =
  `!n:int32. !mp:wr1_ptr. !up:wr1_ptr. !rp:wr1_ptr. !invm:int64.
     ((&0:int) < ival n /\
      wr1_valid mp (ival n) /\
      wr1_valid up ((&2:int) * ival n) /\
      wr1_valid rp (ival n) /\
      ODD (num_of_int (wr1_value mp (ival n))) /\
      (wr1_value mp (ival n) * wr1_u64 invm) rem wr1_radix =
        wr1_radix - (&1:int) /\
      wr1_writable up /\
      wr1_writable rp)
     ==>
     wr1_minimum up <= wr1_offset up + (&0:int) /\
     wr1_offset up + (&0:int) <= wr1_maximum up /\
     wr1_all_o1 n up rp mp invm`;;

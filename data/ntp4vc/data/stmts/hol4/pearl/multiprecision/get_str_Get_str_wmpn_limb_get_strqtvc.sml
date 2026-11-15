(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/get_str_Get_str_wmpn_limb_get_strqtvc: the loop
  verification condition for converting one 64-bit limb to little-endian
  base digits using reciprocal division, with fixed-width bounds, pointer
  updates, value preservation, digit bounds, and memory framing. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory listTheory wordsTheory;

val _ = type_abbrev
  ("wlg_bptr", ``:word8 list # (int # (int # (int # (bool # 'z))))``);
val _ = type_abbrev ("wlg_info", ``:int # (word32 # word64)``);

val wlg_radix_def = Define `
  wlg_radix = (18446744073709551616 : int)`;

val wlg_to_num_def = Define `
  wlg_to_num (z : int) = if z < (0 : int) then 0 else Num z`;

val wlg_u64_def = Define `
  wlg_u64 (x : word64) = &(w2n x)`;

val wlg_u32_def = Define `
  wlg_u32 (x : word32) = &(w2n x)`;

val wlg_u8_def = Define `
  wlg_u8 (x : word8) = &(w2n x)`;

val wlg_i32_def = Define `
  wlg_i32 (x : word32) = w2i x`;

val wlg_ipow_def = Define `
  wlg_ipow (base : int) (exponent : int) =
    base ** wlg_to_num exponent`;

val wlg_int32_in_bounds_def = Define `
  wlg_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val wlg_uint64_in_bounds_def = Define `
  wlg_uint64_in_bounds (z : int) <=>
    (0 : int) <= z /\ z <= (18446744073709551615 : int)`;

val wlg_info_base_def = Define `
  wlg_info_base (info : wlg_info) = FST info`;

val wlg_data_def = Define `
  wlg_data (p : 'z wlg_bptr) = FST p`;

val wlg_offset_def = Define `
  wlg_offset (p : 'z wlg_bptr) = FST (SND p)`;

val wlg_minimum_def = Define `
  wlg_minimum (p : 'z wlg_bptr) = FST (SND (SND p))`;

val wlg_maximum_def = Define `
  wlg_maximum (p : 'z wlg_bptr) =
    FST (SND (SND (SND p)))`;

val wlg_writable_def = Define `
  wlg_writable (p : 'z wlg_bptr) =
    FST (SND (SND (SND (SND p))))`;

val wlg_zone_def = Define `
  wlg_zone (p : 'z wlg_bptr) =
    SND (SND (SND (SND (SND p))))`;

val wlg_pelts_def = Define `
  wlg_pelts (p : 'z wlg_bptr) (index : int) =
    let k = wlg_to_num index in
      if k < LENGTH (wlg_data p) then
        EL k (wlg_data p)
      else
        (0w : word8)`;

val wlg_valid_def = Define `
  wlg_valid (p : 'z wlg_bptr) (size : int) <=>
    wlg_int32_in_bounds size /\
    (0 : int) <= size /\
    (0 : int) <= wlg_minimum p /\
    wlg_minimum p <= wlg_offset p /\
    wlg_offset p + size <= wlg_maximum p /\
    wlg_maximum p <= &(LENGTH (wlg_data p))`;

val wlg_same_frame_def = Define `
  wlg_same_frame (newer : 'z wlg_bptr) (older : 'z wlg_bptr) <=>
    LENGTH (wlg_data newer) = LENGTH (wlg_data older) /\
    wlg_offset newer = wlg_offset older /\
    wlg_minimum newer = wlg_minimum older /\
    wlg_maximum newer = wlg_maximum older /\
    wlg_writable newer = wlg_writable older /\
    wlg_zone newer = wlg_zone older`;

val wlg_update_def = Define `
  wlg_update (f : int -> 'a) (index : int) (value : 'a) =
    \query. if query = index then value else f query`;

val wlg_reciprocal_def = Define `
  wlg_reciprocal (di : word64) (d1 : word64) <=>
    wlg_u64 di =
      ((wlg_radix * wlg_radix - (1 : int)) / wlg_u64 d1) -
      wlg_radix`;

val wlg_in_base_def = Define `
  wlg_in_base
      (base : int) (m : int -> word8) (lower : int) (upper : int) <=>
    !index : int.
      lower <= index /\ index < upper
      ==>
      (0 : int) <= wlg_u8 (m index) /\
      wlg_u8 (m index) < base`;

val wlg_svalue_le_count_def = Define `
  (wlg_svalue_le_count
      (base : int) (m : int -> word8) (start : int) 0 =
     (0 : int)) /\
  (wlg_svalue_le_count base m start (SUC count) =
     wlg_u8 (m start) +
       base *
         wlg_svalue_le_count
           base m (start + (1 : int)) count)`;

val wlg_svalue_le_def = Define `
  wlg_svalue_le
      (base : int) (p : 'z wlg_bptr) (size : int) =
    wlg_svalue_le_count
      base (wlg_pelts p) (wlg_offset p) (wlg_to_num size)`;

val wlg_loop_state_def = Define `
  wlg_loop_state
      (base : int) (original_w : word64) (original_sp : 'z wlg_bptr)
      (size : word32) (current_sp : 'z wlg_bptr)
      (i : word32) (w : word64) <=>
    ((0 : int) <= wlg_u64 w /\ wlg_u64 w < wlg_radix) /\
    ((0 : int) <= wlg_i32 i /\ wlg_i32 i <= wlg_i32 size) /\
    ((0 : int) < wlg_u64 w
     ==>
     (0 : int) <= wlg_i32 i /\ wlg_i32 i < wlg_i32 size) /\
    wlg_in_base
      base (wlg_pelts current_sp) (wlg_offset current_sp)
      (wlg_offset current_sp + wlg_i32 i) /\
    (wlg_u64 w = (0 : int)
     ==>
     (0 : int) < wlg_i32 i
     ==>
     (0 : int) <
       wlg_u8
         (wlg_pelts current_sp
           (wlg_offset current_sp + wlg_i32 i - (1 : int)))) /\
    wlg_u64 original_w =
      wlg_svalue_le base current_sp (wlg_i32 i) +
        wlg_ipow base (wlg_i32 i) * wlg_u64 w /\
    (!index : int.
       index < wlg_offset current_sp \/
       wlg_offset current_sp + wlg_i32 i <= index
       ==>
       wlg_pelts current_sp index = wlg_pelts original_sp index)`;

val wlg_done_def = Define `
  wlg_done
      (base : int) (original_w : word64) (original_sp : 'z wlg_bptr)
      (size : word32) (current_sp : 'z wlg_bptr) (i : word32) <=>
    (0 : int) <= wlg_i32 i /\
    (!result : word32.
       wlg_u32 result = wlg_i32 i
       ==>
       wlg_svalue_le base current_sp (wlg_u32 result) =
         wlg_u64 original_w /\
       ((0 : int) <= wlg_u32 result /\
        wlg_u32 result <= wlg_i32 size) /\
       ((0 : int) < wlg_u32 result
        ==>
        (0 : int) <
          wlg_u8
            (wlg_pelts current_sp
              (wlg_offset current_sp +
               wlg_u32 result - (1 : int)))) /\
       (!index : int.
          index < wlg_offset current_sp \/
          wlg_offset current_sp + wlg_u32 result <= index
          ==>
          wlg_pelts current_sp index =
            wlg_pelts original_sp index) /\
       wlg_in_base
         base (wlg_pelts current_sp) (wlg_offset current_sp)
         (wlg_offset current_sp + wlg_u32 result))`;

val wlg_positive_step_def = Define `
  wlg_positive_step
      (base : int) (original_w : word64) (original_sp : 'z wlg_bptr)
      (d1 : word64) (shift : word64) (di : word64)
      (size : word32) (current_sp : 'z wlg_bptr)
      (i : word32) (w : word64) <=>
    wlg_uint64_in_bounds ((64 : int) - wlg_u64 shift) /\
    (!o1 : word64.
       wlg_u64 o1 = (64 : int) - wlg_u64 shift
       ==>
       ((0 : int) <= wlg_u64 o1 /\ wlg_u64 o1 < (64 : int)) /\
       (!h : word64.
          wlg_u64 h =
            wlg_u64 w / wlg_ipow (2 : int) (wlg_u64 o1)
          ==>
          ((0 : int) <= wlg_u64 shift /\
           wlg_u64 shift < (64 : int)) /\
          (!l : word64.
             wlg_u64 l =
               (wlg_u64 w *
                  wlg_ipow (2 : int) (wlg_u64 shift)) %
               wlg_radix
             ==>
             (wlg_radix / (2 : int) <= wlg_u64 d1 /\
              wlg_u64 h < wlg_u64 d1 /\
              wlg_reciprocal di d1) /\
             (!q r : word64.
                wlg_u64 q * wlg_u64 d1 + wlg_u64 r =
                    wlg_u64 l + wlg_radix * wlg_u64 h /\
                (0 : int) <= wlg_u64 r /\
                wlg_u64 r < wlg_u64 d1
                ==>
                (((0 : int) <= wlg_u64 shift /\
                  wlg_u64 shift < (64 : int)) /\
                 wlg_u64 r %
                     wlg_ipow (2 : int) (wlg_u64 shift) =
                   (0 : int)) /\
                (!nr : word64.
                   wlg_u64 r =
                     wlg_ipow (2 : int) (wlg_u64 shift) *
                       wlg_u64 nr
                   ==>
                   (((0 : int) <= wlg_u64 shift /\
                     wlg_u64 shift < (64 : int)) /\
                    wlg_u64 r %
                        wlg_ipow (2 : int) (wlg_u64 shift) =
                      (0 : int)) /\
                   (!o2 : word64.
                      wlg_u64 r =
                        wlg_ipow (2 : int) (wlg_u64 shift) *
                          wlg_u64 o2
                      ==>
                      ((0 : int) <= wlg_u64 o2 /\
                       wlg_u64 o2 <= (255 : int)) /\
                      (!o3 : word8.
                         wlg_u8 o3 = wlg_u64 o2
                         ==>
                         ((wlg_minimum current_sp <=
                              wlg_offset current_sp + wlg_i32 i /\
                           wlg_offset current_sp + wlg_i32 i <
                              wlg_maximum current_sp) /\
                          wlg_writable current_sp = T) /\
                         (!next_sp : 'z wlg_bptr.
                            wlg_same_frame next_sp current_sp
                            ==>
                            (wlg_pelts next_sp =
                               wlg_update
                                 (wlg_pelts current_sp)
                                 (wlg_offset next_sp + wlg_i32 i) o3 /\
                             wlg_pelts next_sp
                               (wlg_offset next_sp + wlg_i32 i) = o3)
                            ==>
                            wlg_int32_in_bounds
                              (wlg_i32 i + (1 : int)) /\
                            (!next_i : word32.
                               wlg_i32 next_i =
                                 wlg_i32 i + (1 : int)
                               ==>
                               wlg_u64 q < wlg_u64 w /\
                               wlg_loop_state
                                 base original_w original_sp size
                                 next_sp next_i q)))))))))`;

val get_str_Get_str_wmpn_limb_get_strqtvc_statement =
  ``!info : wlg_info.
    !sp : 'z wlg_bptr.
    !d1 shift di : word64.
    !size : word32.
    !w : word64.
      (2 : int) <= wlg_info_base info ==>
      wlg_info_base info <= (256 : int) ==>
      wlg_writable sp = T ==>
      wlg_radix / (2 : int) <= wlg_u64 d1 ==>
      (0 : int) <= wlg_u64 shift ==>
      wlg_u64 shift <= (63 : int) ==>
      wlg_info_base info *
          wlg_ipow (2 : int) (wlg_u64 shift) =
        wlg_u64 d1 ==>
      wlg_reciprocal di d1 ==>
      wlg_valid sp (wlg_i32 size) ==>
      (0 : int) < wlg_i32 size ==>
      wlg_u64 w <
        wlg_ipow (wlg_info_base info) (wlg_i32 size) ==>
      wlg_loop_state
        (wlg_info_base info) w sp size sp (0w : word32) w /\
      (!i : word32.
       !w1 : word64.
       !sp1 : 'z wlg_bptr.
         wlg_same_frame sp1 sp
         ==>
         wlg_loop_state
           (wlg_info_base info) w sp size sp1 i w1
         ==>
         if (0 : int) < wlg_u64 w1 then
           wlg_positive_step
             (wlg_info_base info) w sp d1 shift di size sp1 i w1
         else
           wlg_done
             (wlg_info_base info) w sp size sp1 i)``;

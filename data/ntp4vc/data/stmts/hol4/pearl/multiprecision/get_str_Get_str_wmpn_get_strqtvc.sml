(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/get_str_Get_str_wmpn_get_strqtvc: the verification
  condition selecting between power-of-two and general-base conversion of a
  positive multiprecision integer to a bounded byte string, preserving its
  value, digit bounds, leading-digit positivity, and memory frame. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory listTheory wordsTheory;

val _ = type_abbrev
  ("gsw_lptr", ``:word64 list # (int # (int # (int # (bool # 'z))))``);
val _ = type_abbrev
  ("gsw_bptr", ``:word8 list # (int # (int # (int # (bool # 'z))))``);
val _ = type_abbrev ("gsw_info", ``:int # (word32 # word64)``);

val gsw_radix_def = Define `
  gsw_radix = (18446744073709551616 : int)`;

val gsw_to_num_def = Define `
  gsw_to_num (z : int) = if z < (0 : int) then 0 else Num z`;

val gsw_u64_def = Define `
  gsw_u64 (x : word64) = &(w2n x)`;

val gsw_u32_def = Define `
  gsw_u32 (x : word32) = &(w2n x)`;

val gsw_u8_def = Define `
  gsw_u8 (x : word8) = &(w2n x)`;

val gsw_i32_def = Define `
  gsw_i32 (x : word32) = w2i x`;

val gsw_int32_in_bounds_def = Define `
  gsw_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val gsw_ipow_def = Define `
  gsw_ipow (base : int) (exponent : int) =
    base ** gsw_to_num exponent`;

val gsw_ldata_def = Define `
  gsw_ldata (p : 'z gsw_lptr) = FST p`;

val gsw_bdata_def = Define `
  gsw_bdata (p : 'z gsw_bptr) = FST p`;

val gsw_loffset_def = Define `
  gsw_loffset (p : 'z gsw_lptr) = FST (SND p)`;

val gsw_boffset_def = Define `
  gsw_boffset (p : 'z gsw_bptr) = FST (SND p)`;

val gsw_lminimum_def = Define `
  gsw_lminimum (p : 'z gsw_lptr) = FST (SND (SND p))`;

val gsw_bminimum_def = Define `
  gsw_bminimum (p : 'z gsw_bptr) = FST (SND (SND p))`;

val gsw_lmaximum_def = Define `
  gsw_lmaximum (p : 'z gsw_lptr) = FST (SND (SND (SND p)))`;

val gsw_bmaximum_def = Define `
  gsw_bmaximum (p : 'z gsw_bptr) = FST (SND (SND (SND p)))`;

val gsw_lwritable_def = Define `
  gsw_lwritable (p : 'z gsw_lptr) =
    FST (SND (SND (SND (SND p))))`;

val gsw_bwritable_def = Define `
  gsw_bwritable (p : 'z gsw_bptr) =
    FST (SND (SND (SND (SND p))))`;

val gsw_lzone_def = Define `
  gsw_lzone (p : 'z gsw_lptr) =
    SND (SND (SND (SND (SND p))))`;

val gsw_bzone_def = Define `
  gsw_bzone (p : 'z gsw_bptr) =
    SND (SND (SND (SND (SND p))))`;

val gsw_lpelts_def = Define `
  gsw_lpelts (p : 'z gsw_lptr) (index : int) =
    let k = gsw_to_num index in
      if k < LENGTH (gsw_ldata p) then
        EL k (gsw_ldata p)
      else
        (0w : word64)`;

val gsw_bpelts_def = Define `
  gsw_bpelts (p : 'z gsw_bptr) (index : int) =
    let k = gsw_to_num index in
      if k < LENGTH (gsw_bdata p) then
        EL k (gsw_bdata p)
      else
        (0w : word8)`;

val gsw_lvalid_def = Define `
  gsw_lvalid (p : 'z gsw_lptr) (size : int) <=>
    gsw_int32_in_bounds size /\
    (0 : int) <= size /\
    (0 : int) <= gsw_lminimum p /\
    gsw_lminimum p <= gsw_loffset p /\
    gsw_loffset p + size <= gsw_lmaximum p /\
    gsw_lmaximum p <= &(LENGTH (gsw_ldata p))`;

val gsw_bvalid_def = Define `
  gsw_bvalid (p : 'z gsw_bptr) (size : int) <=>
    gsw_int32_in_bounds size /\
    (0 : int) <= size /\
    (0 : int) <= gsw_bminimum p /\
    gsw_bminimum p <= gsw_boffset p /\
    gsw_boffset p + size <= gsw_bmaximum p /\
    gsw_bmaximum p <= &(LENGTH (gsw_bdata p))`;

val gsw_same_bframe_def = Define `
  gsw_same_bframe (newer : 'z gsw_bptr) (older : 'z gsw_bptr) <=>
    LENGTH (gsw_bdata newer) = LENGTH (gsw_bdata older) /\
    gsw_boffset newer = gsw_boffset older /\
    gsw_bminimum newer = gsw_bminimum older /\
    gsw_bmaximum newer = gsw_bmaximum older /\
    gsw_bwritable newer = gsw_bwritable older /\
    gsw_bzone newer = gsw_bzone older`;

val gsw_value_count_def = Define `
  (gsw_value_count (p : 'z gsw_lptr) (start : int) 0 =
     (0 : int)) /\
  (gsw_value_count p start (SUC count) =
     gsw_u64 (gsw_lpelts p start) +
       gsw_radix * gsw_value_count p (start + (1 : int)) count)`;

val gsw_value_def = Define `
  gsw_value (p : 'z gsw_lptr) (size : int) =
    gsw_value_count p (gsw_loffset p) (gsw_to_num size)`;

val gsw_svalue_count_def = Define `
  (gsw_svalue_count
      (base : int) (m : int -> word8) (start : int) 0 =
     (0 : int)) /\
  (gsw_svalue_count base m start (SUC count) =
     gsw_u8 (m (start + &(SUC count) - (1 : int))) +
       base * gsw_svalue_count base m start count)`;

val gsw_svalue_def = Define `
  gsw_svalue (base : int) (p : 'z gsw_bptr) (size : int) =
    gsw_svalue_count
      base (gsw_bpelts p) (gsw_boffset p) (gsw_to_num size)`;

val gsw_in_base_def = Define `
  gsw_in_base
      (base : int) (m : int -> word8) (lower : int) (upper : int) <=>
    !index : int.
      lower <= index /\ index < upper
      ==>
      (0 : int) <= gsw_u8 (m index) /\
      gsw_u8 (m index) < base`;

val gsw_bframe_def = Define `
  gsw_bframe
      (newer : 'z gsw_bptr) (older : 'z gsw_bptr) (capacity : int) <=>
    !index : int.
      index < gsw_boffset newer \/
      gsw_boffset newer + capacity <= index
      ==>
      gsw_bpelts newer index = gsw_bpelts older index`;

val gsw_info_base_def = Define `
  gsw_info_base (info : gsw_info) = FST info`;

val gsw_info_exp_def = Define `
  gsw_info_exp (info : gsw_info) = FST (SND info)`;

val gsw_info_bb_def = Define `
  gsw_info_bb (info : gsw_info) = SND (SND info)`;

val gsw_info_invariant_def = Define `
  gsw_info_invariant (info : gsw_info) <=>
    (2 : int) <= gsw_info_base info /\
    gsw_info_base info <= (256 : int) /\
    gsw_u64 (gsw_info_bb info) < gsw_radix /\
    gsw_radix <=
      gsw_u64 (gsw_info_bb info) * gsw_info_base info /\
    (7 : int) <= gsw_u32 (gsw_info_exp info) /\
    gsw_u32 (gsw_info_exp info) <= (63 : int) /\
    gsw_u64 (gsw_info_bb info) =
      gsw_ipow
        (gsw_info_base info) (gsw_u32 (gsw_info_exp info))`;

val gsw_final_post_def = Define `
  gsw_final_post
      (base : word32) (up : 'z gsw_lptr) (un : word32)
      (sz : word32) (sp1 : 'z gsw_bptr) (result : word32) <=>
    gsw_in_base
      (gsw_i32 base)
      (gsw_bpelts sp1)
      (gsw_boffset sp1)
      (gsw_boffset sp1 + gsw_u32 result) /\
    gsw_svalue (gsw_i32 base) sp1 (gsw_u32 result) =
      gsw_value up (gsw_i32 un) /\
    ((0 : int) < gsw_u32 result /\
     gsw_u32 result < gsw_i32 sz) /\
    (0 : int) <
      gsw_u8 (gsw_bpelts sp1 (gsw_boffset sp1))`;

val gsw_bits_capacity_def = Define `
  gsw_bits_capacity (o2 : word32) (bits : word32) =
    (gsw_i32 o2 + gsw_u32 bits - (1 : int)) / gsw_u32 bits`;

val gsw_bits_pre_def = Define `
  gsw_bits_pre
      (up : 'z gsw_lptr) (un : word32)
      (sp : 'z gsw_bptr) (bits : word32) (o2 : word32) <=>
    (1 : int) <= gsw_i32 un /\
    gsw_lvalid up (gsw_i32 un) /\
    ((1 : int) <= gsw_u32 bits /\
     gsw_u32 bits <= (8 : int)) /\
    gsw_bvalid sp (gsw_bits_capacity o2 bits) /\
    (0 : int) <= gsw_i32 o2 /\
    gsw_value up (gsw_i32 un) <
      gsw_ipow (2 : int) (gsw_i32 o2) /\
    (0 : int) <
      gsw_u64
        (gsw_lpelts up
          (gsw_loffset up + gsw_i32 un - (1 : int))) /\
    (64 : int) * gsw_i32 un + (7 : int) <=
      (2147483647 : int) /\
    gsw_bwritable sp = T`;

val gsw_bits_result_pre_def = Define `
  gsw_bits_result_pre
      (up : 'z gsw_lptr) (un : word32)
      (sp : 'z gsw_bptr) (sp1 : 'z gsw_bptr)
      (bits : word32) (o2 : word32) (result : word32) <=>
    gsw_in_base
      (gsw_ipow (2 : int) (gsw_u32 bits))
      (gsw_bpelts sp1)
      (gsw_boffset sp1)
      (gsw_boffset sp1 + gsw_u32 result) /\
    gsw_svalue
      (gsw_ipow (2 : int) (gsw_u32 bits))
      sp1 (gsw_u32 result) =
      gsw_value up (gsw_i32 un) /\
    ((0 : int) < gsw_u32 result /\
     gsw_u32 result <= gsw_bits_capacity o2 bits) /\
    (0 : int) <
      gsw_u8 (gsw_bpelts sp1 (gsw_boffset sp1)) /\
    gsw_bframe sp1 sp (gsw_bits_capacity o2 bits)`;

val gsw_bits_continuation_def = Define `
  gsw_bits_continuation
      (base : word32) (up : 'z gsw_lptr) (un : word32)
      (sp : 'z gsw_bptr) (sz : word32)
      (bits : word32) (o2 : word32) <=>
    !sp1 : 'z gsw_bptr.
      gsw_same_bframe sp1 sp
      ==>
      !result : word32.
        gsw_bits_result_pre up un sp sp1 bits o2 result
        ==>
        gsw_final_post base up un sz sp1 result`;

val gsw_bits_branch_def = Define `
  gsw_bits_branch
      (base : word32) (up : 'z gsw_lptr) (un : word32)
      (sp : 'z gsw_bptr) (sz : word32) (bits : word32) <=>
    gsw_int32_in_bounds ((64 : int) * gsw_i32 un) /\
    !o2 : word32.
      gsw_i32 o2 = (64 : int) * gsw_i32 un
      ==>
      gsw_bits_pre up un sp bits o2 /\
      gsw_bits_continuation base up un sp sz bits o2`;

val gsw_other_pre_def = Define `
  gsw_other_pre
      (base : word32) (up : 'z gsw_lptr) (un : word32)
      (sp : 'z gsw_bptr) (sz : word32) (info : gsw_info) <=>
    gsw_lvalid up (gsw_i32 un) /\
    (1 : int) <= gsw_i32 un /\
    gsw_info_base info = gsw_i32 base /\
    gsw_lwritable up = T /\
    gsw_bwritable sp = T /\
    (0 : int) <
      gsw_u64
        (gsw_lpelts up
          (gsw_loffset up + gsw_i32 un - (1 : int))) /\
    (0 : int) < gsw_i32 sz /\
    gsw_bvalid sp (gsw_i32 sz) /\
    gsw_value up (gsw_i32 un) <
      gsw_ipow (gsw_i32 base) (gsw_i32 sz - (1 : int))`;

val gsw_other_result_pre_def = Define `
  gsw_other_result_pre
      (base : word32) (up : 'z gsw_lptr) (un : word32)
      (sp : 'z gsw_bptr) (sz : word32)
      (sp1 : 'z gsw_bptr) (result : word32) <=>
    ((0 : int) <= gsw_u32 result /\
     gsw_u32 result < gsw_i32 sz) /\
    gsw_svalue (gsw_i32 base) sp1 (gsw_u32 result) =
      gsw_value up (gsw_i32 un) /\
    gsw_in_base
      (gsw_i32 base)
      (gsw_bpelts sp1)
      (gsw_boffset sp1)
      (gsw_boffset sp1 + gsw_u32 result) /\
    (0 : int) <
      gsw_u8 (gsw_bpelts sp1 (gsw_boffset sp1)) /\
    gsw_bframe sp1 sp (gsw_i32 sz)`;

val gsw_other_continuation_def = Define `
  gsw_other_continuation
      (base : word32) (up : 'z gsw_lptr) (un : word32)
      (sp : 'z gsw_bptr) (sz : word32) <=>
    !sp1 : 'z gsw_bptr.
      gsw_same_bframe sp1 sp
      ==>
      !result : word32.
        gsw_other_result_pre base up un sp sz sp1 result
        ==>
        gsw_final_post base up un sz sp1 result`;

val gsw_other_branch_def = Define `
  gsw_other_branch
      (base : word32) (up : 'z gsw_lptr) (un : word32)
      (sp : 'z gsw_bptr) (sz : word32) <=>
    (0 : int) <= gsw_i32 base /\
    !o2 : word64.
      gsw_u64 o2 = gsw_i32 base
      ==>
      ((2 : int) <= gsw_u64 o2 /\
       gsw_u64 o2 <= (256 : int)) /\
      !info : gsw_info.
        gsw_info_invariant info /\
        gsw_info_base info = gsw_u64 o2
        ==>
        gsw_other_pre base up un sp sz info /\
        gsw_other_continuation base up un sp sz`;

val gsw_power_of_two_contract_def = Define `
  gsw_power_of_two_contract (o1 : word64) (bits : word32) <=>
    ((0 : int) <= gsw_u32 bits /\
     gsw_u32 bits <= (8 : int)) /\
    (gsw_u32 bits <> (0 : int)
     ==>
     gsw_ipow (2 : int) (gsw_u32 bits) = gsw_u64 o1) /\
    (gsw_u32 bits = (0 : int)
     ==>
     !n : int.
       (0 : int) <= n
       ==>
       gsw_ipow (2 : int) n <> gsw_u64 o1)`;

val get_str_Get_str_wmpn_get_strqtvc_statement =
  ``!sz : word32.
    !un : word32.
    !sp : 'z gsw_bptr.
    !up : 'z gsw_lptr.
    !base : word32.
      (0 : int) < gsw_i32 sz ==>
      (0 : int) < gsw_i32 un ==>
      gsw_bvalid sp (gsw_i32 sz) ==>
      gsw_lvalid up (gsw_i32 un) ==>
      gsw_bwritable sp = T ==>
      gsw_lwritable up = T ==>
      gsw_ipow gsw_radix (gsw_i32 un) <=
        gsw_ipow (gsw_i32 base) (gsw_i32 sz - (1 : int)) ==>
      (0 : int) <
        gsw_u64
          (gsw_lpelts up
            (gsw_loffset up + gsw_i32 un - (1 : int))) ==>
      (2 : int) <= gsw_i32 base ==>
      gsw_i32 base <= (256 : int) ==>
      (64 : int) * gsw_i32 un + (7 : int) <=
        (2147483647 : int) ==>
      (0 : int) <= gsw_i32 base /\
      !o1 : word64.
        gsw_u64 o1 = gsw_i32 base
        ==>
        ((2 : int) <= gsw_u64 o1 /\
         gsw_u64 o1 <= (256 : int)) /\
        !bits : word32.
          gsw_power_of_two_contract o1 bits
          ==>
          (gsw_u32 bits = (0 : int)
           ==>
           bits = (0w : word32))
          ==>
          if ~(bits = (0w : word32)) then
            gsw_bits_branch base up un sp sz bits
          else
            gsw_other_branch base up un sp sz``;

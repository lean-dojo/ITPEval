(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/get_str_Get_str_wmpn_get_str_otherqtvc: the verification
  condition for converting a positive multiprecision integer to digits in an
  arbitrary base, including normalized division, zero padding, byte reversal,
  pointer frames, and the final string-value contract. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory listTheory wordsTheory;

val _ = type_abbrev
  ("gso_lptr", ``:word64 list # (int # (int # (int # (bool # 'z))))``);
val _ = type_abbrev
  ("gso_bptr", ``:word8 list # (int # (int # (int # (bool # 'z))))``);
val _ = type_abbrev ("gso_info", ``:int # (word32 # word64)``);

val gso_radix_def = Define `
  gso_radix = (18446744073709551616 : int)`;

val gso_to_num_def = Define `
  gso_to_num (z : int) = if z < (0 : int) then 0 else Num z`;

val gso_u64_def = Define `
  gso_u64 (x : word64) = &(w2n x)`;

val gso_u32_def = Define `
  gso_u32 (x : word32) = &(w2n x)`;

val gso_u8_def = Define `
  gso_u8 (x : word8) = &(w2n x)`;

val gso_i32_def = Define `
  gso_i32 (x : word32) = w2i x`;

val gso_i32_bounds_def = Define `
  gso_i32_bounds (x : int) <=>
    -(2147483648 : int) <= x /\ x <= (2147483647 : int)`;

val gso_u32_bounds_def = Define `
  gso_u32_bounds (x : int) <=>
    (0 : int) <= x /\ x <= (4294967295 : int)`;

val gso_ipow_def = Define `
  gso_ipow (b : int) (e : int) = b ** gso_to_num e`;

val gso_ldata_def = Define `gso_ldata (p:'z gso_lptr) = FST p`;
val gso_bdata_def = Define `gso_bdata (p:'z gso_bptr) = FST p`;
val gso_loff_def = Define `gso_loff (p:'z gso_lptr) = FST (SND p)`;
val gso_boff_def = Define `gso_boff (p:'z gso_bptr) = FST (SND p)`;
val gso_lmin_def = Define
  `gso_lmin (p:'z gso_lptr) = FST (SND (SND p))`;
val gso_bmin_def = Define
  `gso_bmin (p:'z gso_bptr) = FST (SND (SND p))`;
val gso_lmax_def = Define
  `gso_lmax (p:'z gso_lptr) = FST (SND (SND (SND p)))`;
val gso_bmax_def = Define
  `gso_bmax (p:'z gso_bptr) = FST (SND (SND (SND p)))`;
val gso_lwrite_def = Define
  `gso_lwrite (p:'z gso_lptr) = FST (SND (SND (SND (SND p))))`;
val gso_bwrite_def = Define
  `gso_bwrite (p:'z gso_bptr) = FST (SND (SND (SND (SND p))))`;
val gso_lzone_def = Define
  `gso_lzone (p:'z gso_lptr) = SND (SND (SND (SND (SND p))))`;
val gso_bzone_def = Define
  `gso_bzone (p:'z gso_bptr) = SND (SND (SND (SND (SND p))))`;

val gso_lpelts_def = Define
  `gso_lpelts p (i:int) =
     let k = gso_to_num i in
     if k < LENGTH (gso_ldata p) then EL k (gso_ldata p)
     else (0w : word64)`;
val gso_bpelts_def = Define
  `gso_bpelts p (i:int) =
     let k = gso_to_num i in
     if k < LENGTH (gso_bdata p) then EL k (gso_bdata p)
     else (0w : word8)`;

val gso_lvalid_def = Define
  `gso_lvalid p (n:int) <=>
     gso_i32_bounds n /\ (0 : int) <= n /\
     (0 : int) <= gso_lmin p /\ gso_lmin p <= gso_loff p /\
     gso_loff p + n <= gso_lmax p /\
     gso_lmax p <= &(LENGTH (gso_ldata p))`;
val gso_bvalid_def = Define
  `gso_bvalid p (n:int) <=>
     gso_i32_bounds n /\ (0 : int) <= n /\
     (0 : int) <= gso_bmin p /\ gso_bmin p <= gso_boff p /\
     gso_boff p + n <= gso_bmax p /\
     gso_bmax p <= &(LENGTH (gso_bdata p))`;
val gso_laccess_def = Define
  `gso_laccess p (i:int) <=> gso_lmin p <= i /\ i < gso_lmax p`;
val gso_baccess_def = Define
  `gso_baccess p (i:int) <=> gso_bmin p <= i /\ i < gso_bmax p`;

val gso_same_lframe_def = Define
  `gso_same_lframe newer older <=>
     LENGTH (gso_ldata newer) = LENGTH (gso_ldata older) /\
     gso_loff newer = gso_loff older /\
     gso_lmin newer = gso_lmin older /\
     gso_lmax newer = gso_lmax older /\
     gso_lwrite newer = gso_lwrite older /\
     gso_lzone newer = gso_lzone older`;
val gso_same_bframe_def = Define
  `gso_same_bframe newer older <=>
     LENGTH (gso_bdata newer) = LENGTH (gso_bdata older) /\
     gso_boff newer = gso_boff older /\
     gso_bmin newer = gso_bmin older /\
     gso_bmax newer = gso_bmax older /\
     gso_bwrite newer = gso_bwrite older /\
     gso_bzone newer = gso_bzone older`;
val gso_shifted_def = Define
  `gso_shifted shifted original (n:int) <=>
     gso_boff shifted = gso_boff original + n /\
     LENGTH (gso_bdata shifted) = LENGTH (gso_bdata original) /\
     gso_bdata shifted = gso_bdata original /\
     gso_bmin shifted = gso_bmin original /\
     gso_bmax shifted = gso_bmax original /\
     gso_bzone shifted = gso_bzone original /\
     gso_bwrite shifted = gso_bwrite original`;
val gso_update_def = Define
  `gso_update (f : int -> 'a) (i : int) (x : 'a) =
     \j. if j = i then x else f j`;

val gso_value_count_def = Define `
  (gso_value_count p (start : int) 0 = (0 : int)) /\
  (gso_value_count p start (SUC count) =
     gso_u64 (gso_lpelts p start) +
     gso_radix * gso_value_count p (start + (1 : int)) count)`;

val gso_value_def = Define `
  gso_value p (n : int) =
    gso_value_count p (gso_loff p) (gso_to_num n)`;

val gso_svalue_le_count_def = Define `
  (gso_svalue_le_count b (m : int -> word8) (start : int) 0 =
     (0 : int)) /\
  (gso_svalue_le_count b m start (SUC count) =
     gso_u8 (m start) +
     b * gso_svalue_le_count b m (start + (1 : int)) count)`;

val gso_svalue_le_sub_def = Define `
  gso_svalue_le_sub (b : int) (m : int -> word8)
      (lo : int) (hi : int) =
    gso_svalue_le_count b m lo (gso_to_num (hi - lo))`;

val gso_svalue_le_def = Define
  `gso_svalue_le (b:int) p (n:int) =
     gso_svalue_le_sub b (gso_bpelts p) (gso_boff p) (gso_boff p + n)`;

val gso_svalue_sub_count_def = Define `
  (gso_svalue_sub_count b (m : int -> word8) (start : int) 0 =
     (0 : int)) /\
  (gso_svalue_sub_count b m start (SUC count) =
     gso_u8 (m (start + &(SUC count) - (1 : int))) +
     b * gso_svalue_sub_count b m start count)`;

val gso_svalue_sub_def = Define `
  gso_svalue_sub (b : int) (m : int -> word8)
      (lo : int) (hi : int) =
    gso_svalue_sub_count b m lo (gso_to_num (hi - lo))`;
val gso_svalue_def = Define
  `gso_svalue (b:int) p (n:int) =
     gso_svalue_sub b (gso_bpelts p) (gso_boff p) (gso_boff p + n)`;
val gso_in_base_def = Define
  `gso_in_base (b:int) (m:int->word8) (lo:int) (hi:int) <=>
     !i:int. lo <= i /\ i < hi ==> (0 : int) <= gso_u8 (m i) /\
                                      gso_u8 (m i) < b`;
val gso_bframe_def = Define
  `gso_bframe newer older (n:int) <=>
     !i:int. i < gso_boff newer \/ gso_boff newer + n <= i
             ==> gso_bpelts newer i = gso_bpelts older i`;
val gso_lframe_def = Define
  `gso_lframe newer older (n:int) <=>
     !i:int. i < gso_loff newer \/ gso_loff newer + n <= i
             ==> gso_lpelts newer i = gso_lpelts older i`;
val gso_map_eq_def = Define
  `gso_map_eq x y (xi:int) (yi:int) (n:int) <=>
     !i:int. (0 : int) <= i /\ i < n
             ==> gso_lpelts x (xi + i) = gso_lpelts y (yi + i)`;

val gso_info_b_def = Define `gso_info_b (q:gso_info) = FST q`;
val gso_info_exp_def = Define `gso_info_exp (q:gso_info) = FST (SND q)`;
val gso_info_bb_def = Define `gso_info_bb (q:gso_info) = SND (SND q)`;
val gso_info_ok_def = Define
  `gso_info_ok q <=>
     (2 : int) <= gso_info_b q /\ gso_info_b q <= (256 : int) /\
     gso_u64 (gso_info_bb q) < gso_radix /\
     gso_radix <= gso_u64 (gso_info_bb q) * gso_info_b q /\
     (7 : int) <= gso_u32 (gso_info_exp q) /\
     gso_u32 (gso_info_exp q) <= (63 : int) /\
     gso_u64 (gso_info_bb q) =
       gso_ipow (gso_info_b q) (gso_u32 (gso_info_exp q))`;
val gso_reciprocal_def = Define
  `gso_reciprocal di d1 <=>
     gso_u64 di =
       ((gso_radix * gso_radix - (1 : int)) / gso_u64 d1) -
       gso_radix`;
val gso_division_def = Define
  `gso_division quotient dividend count divisor remainder <=>
     gso_value dividend (gso_i32 count) =
       gso_value quotient (gso_i32 count) * gso_u64 divisor +
       gso_u64 remainder /\
     gso_u64 remainder < gso_u64 divisor`;
val gso_allocated_def = Define
  `gso_allocated p (n:int) <=>
     &(LENGTH (gso_ldata p)) = n /\
     gso_loff p = (0 : int) /\ gso_lmin p = (0 : int) /\
     gso_lmax p = n /\ gso_lwrite p = T`;

val gso_limb_post_def = Define
  `gso_limb_post b before after capacity input done <=>
     gso_svalue_le b after (gso_u32 done) = gso_u64 input /\
     ((0 : int) <= gso_u32 done /\ gso_u32 done <= capacity) /\
     ((0 : int) < gso_u32 done ==>
       (0 : int) < gso_u8 (gso_bpelts after
         (gso_boff after + gso_u32 done - (1 : int)))) /\
     gso_bframe after before (gso_u32 done) /\
     gso_in_base b (gso_bpelts after) (gso_boff after)
       (gso_boff after + gso_u32 done)`;
val gso_partial_def = Define
  `gso_partial total b original_sp size up current_sp sn <=>
     gso_svalue_le b current_sp (gso_i32 sn) +
       gso_ipow b (gso_i32 sn) * gso_value up (1 : int) = total /\
     gso_in_base b (gso_bpelts current_sp) (gso_boff current_sp)
       (gso_boff current_sp + gso_i32 sn) /\
     ((0 : int) <= gso_i32 sn /\ gso_i32 sn < gso_i32 size) /\
     (0 : int) < gso_value up (1 : int) /\
     gso_bframe current_sp original_sp (gso_i32 size)`;
val gso_outer_inv_def = Define
  `gso_outer_inv total b info un size original_sp loopi up n sp sn <=>
     gso_svalue_le b sp (gso_i32 sn) +
       gso_ipow b (gso_i32 sn) * gso_value up (gso_i32 n) = total /\
     ((1 : int) <= gso_i32 n /\ gso_i32 n <= gso_i32 un) /\
     gso_i32 un - gso_i32 n <= loopi /\
     ((0 : int) <= gso_i32 sn /\ gso_i32 sn < gso_i32 size) /\
     gso_i32 sn = loopi * gso_u32 (gso_info_exp info) /\
     gso_in_base b (gso_bpelts sp) (gso_boff sp)
       (gso_boff sp + gso_i32 sn) /\
     (0 : int) < gso_u64 (gso_lpelts up
       (gso_loff up + gso_i32 n - (1 : int))) /\
     gso_bframe sp original_sp (gso_i32 size)`;
val gso_padding_inv_def = Define
  `gso_padding_inv total b info size original_sp up n initial_sn
                   done current_sn sp <=>
     gso_u32 done <= gso_u32 (gso_info_exp info) /\
     gso_i32 current_sn = gso_i32 initial_sn + gso_u32 done /\
     gso_in_base b (gso_bpelts sp) (gso_boff sp)
       (gso_boff sp + gso_i32 current_sn) /\
     gso_svalue_le b sp (gso_i32 current_sn) +
       gso_ipow b
         (gso_i32 current_sn - gso_u32 done +
          gso_u32 (gso_info_exp info)) *
       gso_value up (gso_i32 n) = total /\
     gso_bframe sp original_sp (gso_i32 size)`;

val gso_reverse_inv_def = Define
  `gso_reverse_inv b size original_sp reversal_original current total i <=>
     ((0 : int) <= (2 : int) * gso_i32 i + (1 : int) /\
      (2 : int) * gso_i32 i + (1 : int) <= gso_i32 total + (1 : int)) /\
     (!j:int. gso_boff current + gso_i32 i <= j /\
              j < gso_boff current + gso_i32 total - gso_i32 i
              ==> gso_bpelts current j = gso_bpelts reversal_original j) /\
     gso_in_base b (gso_bpelts current) (gso_boff current)
       (gso_boff current + gso_i32 total) /\
     gso_svalue_sub b (gso_bpelts current) (gso_boff current)
       (gso_boff current + gso_i32 i) =
       gso_svalue_le_sub b (gso_bpelts reversal_original)
         (gso_boff current + gso_i32 total - gso_i32 i)
         (gso_boff current + gso_i32 total) /\
     gso_svalue_sub b (gso_bpelts current)
       (gso_boff current + gso_i32 total - gso_i32 i)
       (gso_boff current + gso_i32 total) =
       gso_svalue_le_sub b (gso_bpelts reversal_original)
         (gso_boff current) (gso_boff current + gso_i32 i) /\
     gso_svalue_le_sub b (gso_bpelts current)
       (gso_boff current + gso_i32 i)
       (gso_boff current + gso_i32 total - gso_i32 i) =
       gso_svalue_le_sub b (gso_bpelts reversal_original)
         (gso_boff current + gso_i32 i)
         (gso_boff current + gso_i32 total - gso_i32 i) /\
     ((0 : int) < gso_i32 i ==>
       (0 : int) < gso_u8 (gso_bpelts current (gso_boff current))) /\
     gso_bframe current original_sp (gso_i32 size)`;
val gso_final_post_def = Define
  `gso_final_post b original_up un original_sp size current result <=>
     ((0 : int) <= gso_u32 result /\ gso_u32 result < gso_i32 size) /\
     gso_svalue b current (gso_u32 result) =
       gso_value original_up (gso_i32 un) /\
     gso_in_base b (gso_bpelts current) (gso_boff current)
       (gso_boff current + gso_u32 result) /\
     (0 : int) < gso_u8 (gso_bpelts current (gso_boff current)) /\
     gso_bframe current original_sp (gso_i32 size)`;

val gso_reverse_swap_def = Define
  `gso_reverse_swap b original_sp size rev total current i <=>
     gso_baccess current (gso_boff current + gso_i32 i) /\
     (!saved:word8.
        saved = gso_bpelts current (gso_boff current + gso_i32 i)
        ==> gso_i32_bounds (gso_i32 total - gso_i32 i) /\
            (!from_end:word32.
               gso_i32 from_end = gso_i32 total - gso_i32 i
               ==> gso_i32_bounds (gso_i32 from_end - (1 : int)) /\
                   (!mirror:word32.
                      gso_i32 mirror = gso_i32 from_end - (1 : int)
                      ==> gso_baccess current
                            (gso_boff current + gso_i32 mirror) /\
                          (!other:word8.
                             other = gso_bpelts current
                               (gso_boff current + gso_i32 mirror)
                             ==> (gso_baccess current
                                    (gso_boff current + gso_i32 i) /\
                                  gso_bwrite current = T) /\
                                 (!after1:'z gso_bptr.
                                    gso_same_bframe after1 current /\
                                    gso_bpelts after1 =
                                      gso_update (gso_bpelts current)
                                        (gso_boff after1 + gso_i32 i) other /\
                                    gso_bpelts after1
                                      (gso_boff after1 + gso_i32 i) = other
                                    ==> gso_i32_bounds
                                          (gso_i32 total - gso_i32 i) /\
                                        (!from_end2:word32.
                                           gso_i32 from_end2 =
                                             gso_i32 total - gso_i32 i
                                           ==> gso_i32_bounds
                                                 (gso_i32 from_end2 -
                                                  (1 : int)) /\
                                               (!mirror2:word32.
                                                  gso_i32 mirror2 =
                                                    gso_i32 from_end2 -
                                                    (1 : int)
                                                  ==>
                                                  (gso_baccess after1
                                                     (gso_boff after1 +
                                                      gso_i32 mirror2) /\
                                                   gso_bwrite after1 = T) /\
                                                  (!after2:'z gso_bptr.
                                                     gso_same_bframe
                                                       after2 after1 /\
                                                     gso_bpelts after2 =
                                                       gso_update
                                                         (gso_bpelts after1)
                                                         (gso_boff after2 +
                                                          gso_i32 mirror2)
                                                         saved /\
                                                     gso_bpelts after2
                                                       (gso_boff after2 +
                                                        gso_i32 mirror2) =
                                                       saved
                                                     ==> gso_i32_bounds
                                                           (gso_i32 i +
                                                            (1 : int)) /\
                                                         (!next_i:word32.
                                                            gso_i32 next_i =
                                                              gso_i32 i +
                                                              (1 : int)
                                                            ==>
                                                            ((0 : int) <=
                                                               gso_i32 total -
                                                               gso_i32 i /\
                                                             gso_i32 total -
                                                               gso_i32 next_i <
                                                             gso_i32 total -
                                                               gso_i32 i) /\
                                                            gso_reverse_inv
                                                              b size
                                                              original_sp
                                                              rev after2
                                                              total
                                                              next_i)))))))))`;

val gso_reverse_done_def = Define
  `gso_reverse_done b original_up un original_sp size current total <=>
     (0 : int) <= gso_i32 total /\
     (!result:word32.
        gso_u32 result = gso_i32 total
        ==> gso_final_post b original_up un original_sp size current result)`;

val gso_reverse_step_def = Define
  `gso_reverse_step b original_up un original_sp size rev total current i <=>
     gso_i32_bounds ((2 : int) * gso_i32 i) /\
     (!twice:word32.
        gso_i32 twice = (2 : int) * gso_i32 i
        ==> gso_i32_bounds (gso_i32 twice + (1 : int)) /\
            (!test:word32.
               gso_i32 test = gso_i32 twice + (1 : int)
               ==> (if gso_i32 test < gso_i32 total then
                      gso_reverse_swap
                        b original_sp size rev total current i
                    else
                      gso_reverse_done
                        b original_up un original_sp size current total)))`;

val gso_reverse_loop_def = Define
  `gso_reverse_loop b original_up un original_sp size rev total <=>
     gso_reverse_inv b size original_sp rev rev total (0w : word32) /\
     (!i:word32. !current:'z gso_bptr.
        gso_same_bframe current rev /\
        gso_reverse_inv b size original_sp rev current total i
        ==> gso_reverse_step b original_up un original_sp size rev
              total current i)`;

val gso_final_limb_return_def = Define
  `gso_final_limb_return
      b original_up un original_sp size current_sp sn spn capacity last <=>
     !after_local:'z gso_bptr. !returned:'z gso_bptr.
       gso_bpelts after_local = gso_bpelts returned /\
       gso_same_bframe after_local spn /\
       gso_same_bframe returned current_sp
       ==> (!done:word32.
              gso_limb_post
                b spn after_local (gso_i32 capacity) last done
              ==> gso_u32 done <= (2147483647 : int) /\
                  (!done_i:word32.
                     gso_i32 done_i = gso_u32 done
                     ==> gso_i32_bounds
                           (gso_i32 sn + gso_i32 done_i) /\
                         (!total:word32.
                            gso_i32 total =
                              gso_i32 sn + gso_i32 done_i
                            ==> gso_reverse_loop
                                  b original_up un original_sp size
                                  returned total)))`;

val gso_final_limb_def = Define
  `gso_final_limb b original_up un info original_sp size shift d1 di
                  current_up current_sp sn <=>
     gso_laccess current_up (gso_loff current_up) /\
     (!last:word64.
        last = gso_lpelts current_up (gso_loff current_up)
        ==> (gso_bmin current_sp <= gso_boff current_sp + gso_i32 sn /\
             gso_boff current_sp + gso_i32 sn <= gso_bmax current_sp) /\
            (!spn:'z gso_bptr.
               gso_shifted spn current_sp (gso_i32 sn)
               ==> gso_i32_bounds (gso_i32 size - (1 : int)) /\
                   (!size1:word32.
                      gso_i32 size1 = gso_i32 size - (1 : int)
                      ==> gso_i32_bounds (gso_i32 size1 - gso_i32 sn) /\
                          (!capacity:word32.
                             gso_i32 capacity =
                               gso_i32 size1 - gso_i32 sn
                             ==> (((2 : int) <= gso_info_b info /\
                                   gso_info_b info <= (256 : int)) /\
                                  gso_bwrite spn = T /\
                                  gso_radix / (2 : int) <= gso_u64 d1 /\
                                  ((0 : int) <= gso_u64 shift /\
                                   gso_u64 shift <= (63 : int)) /\
                                  gso_info_b info *
                                    gso_ipow (2 : int) (gso_u64 shift) =
                                    gso_u64 d1 /\
                                  gso_reciprocal di d1 /\
                                  gso_bvalid spn (gso_i32 capacity) /\
                                  (0 : int) < gso_i32 capacity /\
                                  gso_u64 last <
                                    gso_ipow (gso_info_b info)
                                      (gso_i32 capacity)) /\
                                  gso_final_limb_return
                                    (gso_info_b info) original_up un
                                    original_sp size current_sp sn spn
                                    capacity last))))`;

val gso_final_cont_def = Define
  `gso_final_cont total b original_up un info original_sp size shift d1 di <=>
     !sn:word32. !up:'z gso_lptr. !sp:'z gso_bptr.
       gso_same_lframe up original_up /\
       gso_same_bframe sp original_sp /\
       gso_partial total b original_sp size up sp sn
       ==> gso_final_limb b original_up un info original_sp size shift d1 di
             up sp sn`;

val gso_padding_step_def = Define
  `gso_padding_step total b info original_sp size un up n initial_sn
                    done sp current_sn previous_up previous_n loopi <=>
     if gso_u32 done < gso_u32 (gso_info_exp info) then
       (gso_baccess sp (gso_boff sp + gso_i32 current_sn) /\
        gso_bwrite sp = T) /\
       (!after:'z gso_bptr.
          gso_same_bframe after sp /\
          gso_bpelts after =
            gso_update (gso_bpelts sp)
              (gso_boff after + gso_i32 current_sn) (0w : word8) /\
          gso_bpelts after (gso_boff after + gso_i32 current_sn) =
            (0w : word8)
          ==> gso_i32_bounds (gso_i32 current_sn + (1 : int)) /\
              (!next_sn:word32.
                 gso_i32 next_sn = gso_i32 current_sn + (1 : int)
                 ==> gso_u32_bounds (gso_u32 done + (1 : int)) /\
                     (!next_done:word32.
                        gso_u32 next_done = gso_u32 done + (1 : int)
                        ==> ((0 : int) <=
                               gso_u32 (gso_info_exp info) - gso_u32 done /\
                             gso_u32 (gso_info_exp info) -
                               gso_u32 next_done <
                             gso_u32 (gso_info_exp info) - gso_u32 done) /\
                            gso_padding_inv total b info size original_sp
                              up n initial_sn next_done next_sn after)))
     else
       ((0 : int) <= gso_value previous_up (gso_i32 previous_n) /\
        gso_value up (gso_i32 n) <
          gso_value previous_up (gso_i32 previous_n)) /\
       gso_outer_inv total b info un size original_sp (loopi + (1 : int))
         up n sp current_sn`;

val gso_after_limb_return_def = Define
  `gso_after_limb_return
      total b info original_sp before_sp size un up n initial_sn input
      previous_up previous_n loopi spn capacity <=>
     !after_local:'z gso_bptr. !returned:'z gso_bptr.
       gso_bpelts after_local = gso_bpelts returned /\
       gso_same_bframe after_local spn /\
       gso_same_bframe returned before_sp
       ==> (!done:word32.
              gso_limb_post
                (gso_info_b info) spn after_local
                (gso_i32 capacity) input done
              ==> gso_u32 done <= (2147483647 : int) /\
                  (!done_i:word32.
                     gso_i32 done_i = gso_u32 done
                     ==> gso_i32_bounds
                           (gso_i32 initial_sn + gso_i32 done_i) /\
                         (!new_sn:word32.
                            gso_i32 new_sn =
                              gso_i32 initial_sn + gso_i32 done_i
                            ==> gso_padding_inv
                                  total b info size original_sp up n
                                  initial_sn done new_sn returned /\
                                (!loop_done:word32.
                                 !loop_sn:word32.
                                 !loop_sp:'z gso_bptr.
                                   gso_same_bframe loop_sp returned /\
                                   gso_padding_inv
                                     total b info size original_sp up n
                                     initial_sn loop_done loop_sn loop_sp
                                   ==> gso_padding_step
                                         total b info original_sp size un
                                         up n initial_sn loop_done loop_sp
                                         loop_sn previous_up previous_n
                                         loopi))))`;

val gso_after_limb_def = Define
  `gso_after_limb total b info original_sp before_sp size un shift d1 di
                  up n initial_sn input previous_up previous_n loopi spn <=>
     gso_u32 (gso_info_exp info) <= (2147483647 : int) /\
     (!signed_exp:word32.
        gso_i32 signed_exp = gso_u32 (gso_info_exp info)
        ==> gso_i32_bounds (gso_i32 signed_exp + (1 : int)) /\
            (!capacity:word32.
               gso_i32 capacity = gso_i32 signed_exp + (1 : int)
               ==> (((2 : int) <= gso_info_b info /\
                     gso_info_b info <= (256 : int)) /\
                    gso_bwrite spn = T /\
                    gso_radix / (2 : int) <= gso_u64 d1 /\
                    ((0 : int) <= gso_u64 shift /\
                     gso_u64 shift <= (63 : int)) /\
                    gso_info_b info * gso_ipow (2 : int) (gso_u64 shift) =
                      gso_u64 d1 /\
                    gso_reciprocal di d1 /\
                    gso_bvalid spn (gso_i32 capacity) /\
                    (0 : int) < gso_i32 capacity /\
                    gso_u64 input <
                      gso_ipow (gso_info_b info) (gso_i32 capacity)) /\
                    gso_after_limb_return
                      total b info original_sp before_sp size un up n
                      initial_sn input previous_up previous_n loopi spn
                      capacity))`;

val gso_outer_step_def = Define
  `gso_outer_step total b info original_sp size original_up un shift d1 di
                  temporary up n sp sn loopi <=>
     if (1 : int) < gso_i32 n then
       (gso_lvalid up (gso_i32 n) /\
        gso_lvalid temporary (gso_i32 n) /\
        gso_lwrite temporary = T /\
        (0 : int) < gso_i32 n /\
        (0 : int) < gso_u64 (gso_info_bb info)) /\
       (!after_div:'z gso_lptr.
          gso_same_lframe after_div temporary
          ==> (!remainder:word64.
                gso_division after_div up n (gso_info_bb info) remainder
                ==> gso_lvalid after_div (gso_i32 n) /\
                    gso_lvalid up (gso_i32 n) /\ gso_lwrite up = T /\
                    (!copied:'z gso_lptr.
                       gso_same_lframe copied up /\
                       gso_map_eq copied after_div (gso_loff copied)
                         (gso_loff after_div) (gso_i32 n) /\
                       gso_lframe copied up (gso_i32 n)
                       ==> gso_i32_bounds (gso_i32 n - (1 : int)) /\
                           (!n1:word32.
                              gso_i32 n1 = gso_i32 n - (1 : int)
                              ==> gso_laccess copied
                                    (gso_loff copied + gso_i32 n1) /\
                                  (!top:word64.
                                     top = gso_lpelts copied
                                       (gso_loff copied + gso_i32 n1)
                                     ==> (!is_zero:bool.
                                           (gso_u64 top = (0 : int)
                                            ==> is_zero = T) /\
                                           (is_zero = T
                                            ==> top = (0w : word64))
                                           ==> (!dec:word32.
                                                 (if is_zero
                                                  then dec = (1w : word32)
                                                  else dec = (0w : word32))
                                                 ==> gso_i32_bounds
                                                       (gso_i32 n -
                                                        gso_i32 dec) /\
                                                     (!next_n:word32.
                                                        gso_i32 next_n =
                                                          gso_i32 n -
                                                          gso_i32 dec
                                                        ==> (gso_bmin sp <=
                                                             gso_boff sp +
                                                             gso_i32 sn /\
                                                             gso_boff sp +
                                                             gso_i32 sn <=
                                                             gso_bmax sp) /\
                                                            (!spn:'z gso_bptr.
                                                               gso_shifted spn
                                                                 sp (gso_i32 sn)
                                                               ==> gso_after_limb
                                                                     total b info
                                                                     original_sp
                                                                     sp size un
                                                                     shift d1 di
                                                                     copied next_n
                                                                     sn remainder
                                                                     up n loopi
                                                                     spn)))))))))
     else gso_partial total b original_sp size up sp sn`;

val gso_partial_block_def = Define
  `gso_partial_block total b info original_up un original_sp size shift d1 di <=>
     if (1 : int) < gso_i32 un then
       (0 : int) <= gso_i32 un /\
       (!count:word32.
          gso_u32 count = gso_i32 un
          ==> (0 : int) <= gso_u32 count /\
              (!temporary:'z gso_lptr.
                 gso_allocated temporary (gso_u32 count)
                 ==> gso_outer_inv total b info un size original_sp (0 : int)
                       original_up un original_sp (0w : word32) /\
                     (!loopi:int. !loop_tmp:'z gso_lptr. !loop_up:'z gso_lptr.
                      !loop_n:word32. !loop_sp:'z gso_bptr. !loop_sn:word32.
                        gso_same_lframe loop_tmp temporary /\
                        gso_same_lframe loop_up original_up /\
                        gso_same_bframe loop_sp original_sp /\
                        gso_outer_inv total b info un size original_sp loopi
                          loop_up loop_n loop_sp loop_sn
                        ==> gso_outer_step total b info original_sp size
                              original_up un shift d1 di loop_tmp loop_up
                              loop_n loop_sp loop_sn loopi)))
     else
       gso_partial total b original_sp size original_up original_sp
         (0w : word32)`;

val gso_body_def = Define
  `gso_body total original_up un b info original_sp size shift d1 di <=>
     gso_partial_block total b info original_up un original_sp size shift d1 di /\
     gso_final_cont total b original_up un info original_sp size shift d1 di`;

val get_str_Get_str_wmpn_get_str_otherqtvc_statement =
  `!up:'z gso_lptr. !un:word32. !base:word32. !info:gso_info.
   !sp:'z gso_bptr. !size:word32.
     gso_info_ok info /\
     gso_lvalid up (gso_i32 un) /\
     (1 : int) <= gso_i32 un /\
     gso_info_b info = gso_i32 base /\
     gso_lwrite up = T /\ gso_bwrite sp = T /\
     (0 : int) < gso_u64 (gso_lpelts up
       (gso_loff up + gso_i32 un - (1 : int))) /\
     (0 : int) < gso_i32 size /\
     gso_bvalid sp (gso_i32 size) /\
     gso_value up (gso_i32 un) <
       gso_ipow (gso_i32 base) (gso_i32 size - (1 : int))
     ==>
     (0 : int) <= gso_i32 base /\
     (!base_limb:word64.
        gso_u64 base_limb = gso_i32 base
        ==> (0 : int) < gso_u64 base_limb /\
            (!count:word32.
               gso_ipow (2 : int) (gso_i32 count) * gso_u64 base_limb <=
                 (18446744073709551615 : int) /\
               (18446744073709551615 : int) <
                 (2 : int) * gso_ipow (2 : int) (gso_i32 count) *
                 gso_u64 base_limb /\
               (0 : int) <= gso_i32 count /\ gso_i32 count < (64 : int)
               ==> (0 : int) <= gso_i32 count /\
                   (!shift:word64.
                      gso_u64 shift = gso_i32 count
                      ==> (0 : int) <= gso_i32 base /\
                          (!base_limb2:word64.
                             gso_u64 base_limb2 = gso_i32 base
                             ==> (((0 : int) <= gso_u64 shift /\
                                   gso_u64 shift < (64 : int)) /\
                                  gso_ipow (2 : int) (gso_u64 shift) *
                                    gso_u64 base_limb2 <=
                                    (18446744073709551615 : int)) /\
                                 (!d1:word64.
                                    gso_u64 d1 =
                                      gso_ipow (2 : int) (gso_u64 shift) *
                                      gso_u64 base_limb2
                                    ==> gso_radix / (2 : int) <=
                                          gso_u64 d1 /\
                                        (!di:word64.
                                           gso_reciprocal di d1
                                           ==> gso_body
                                                 (gso_value up (gso_i32 un))
                                                 up un (gso_i32 base) info sp
                                                 size shift d1 di)))))))`;

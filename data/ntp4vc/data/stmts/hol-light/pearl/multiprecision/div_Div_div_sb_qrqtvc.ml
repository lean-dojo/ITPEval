(*
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/div_Div_div_sb_qrqtvc: the verification condition for
  schoolbook multiprecision quotient-and-remainder division, including its
  pointer frames, loop invariant, quotient estimation, correction branch,
  and final arithmetic relation. This file contains no proof.
*)

let dsb_output = open_out "/dev/null";;
Format.pp_set_formatter_out_channel Format.std_formatter dsb_output;;

needs "Library/words.ml";;
needs "Library/isum.ml";;

new_type_abbrev
  ("dsb_ptr",`:(int64 list)#(int#(int#(int#(bool#Z))))`);;

let dsb_radix = new_definition
  `dsb_radix = (&18446744073709551616:int)`;;

let dsb_u64 = new_definition
  `dsb_u64 (x:int64) = (&(val x):int)`;;

let dsb_int32_in_bounds = new_definition
  `dsb_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let dsb_uint64_in_bounds = new_definition
  `dsb_uint64_in_bounds (z:int) <=>
     (&0:int) <= z /\ z <= (&18446744073709551615:int)`;;

let dsb_ipow = new_definition
  `dsb_ipow (base:int) (exponent:int) =
     base pow (if exponent < (&0:int) then 0 else num_of_int exponent)`;;

let dsb_data = new_definition
  `dsb_data (p:dsb_ptr) = FST p`;;

let dsb_offset = new_definition
  `dsb_offset (p:dsb_ptr) = FST (SND p)`;;

let dsb_minimum = new_definition
  `dsb_minimum (p:dsb_ptr) = FST (SND (SND p))`;;

let dsb_maximum = new_definition
  `dsb_maximum (p:dsb_ptr) =
     FST (SND (SND (SND p)))`;;

let dsb_writable = new_definition
  `dsb_writable (p:dsb_ptr) =
     FST (SND (SND (SND (SND p))))`;;

let dsb_zone = new_definition
  `dsb_zone (p:dsb_ptr) =
     SND (SND (SND (SND (SND p))))`;;

let dsb_pelts = new_definition
  `dsb_pelts p (i:int) =
     if i < (&0:int) then (word 0:int64)
     else
       let k = num_of_int i in
       if k < LENGTH (dsb_data p)
       then EL k (dsb_data p)
       else (word 0:int64)`;;

let dsb_plength = new_definition
  `dsb_plength p = (&(LENGTH (dsb_data p)):int)`;;

let dsb_valid = new_definition
  `dsb_valid p (size:int) <=>
     dsb_int32_in_bounds size /\
     (&0:int) <= size /\
     (&0:int) <= dsb_minimum p /\
     dsb_minimum p <= dsb_offset p /\
     dsb_offset p + size <= dsb_maximum p /\
     dsb_maximum p <= dsb_plength p`;;

let dsb_valid_at_range = new_definition
  `dsb_valid_at_range p (start:int) (size:int) <=>
     dsb_int32_in_bounds size /\
     (&0:int) <= size /\
     (&0:int) <= dsb_minimum p /\
     dsb_minimum p <= start /\
     start + size <= dsb_maximum p /\
     dsb_maximum p <= dsb_plength p`;;

let dsb_access_at = new_definition
  `dsb_access_at p (index:int) <=>
     dsb_minimum p <= index /\ index < dsb_maximum p`;;

let dsb_cursor_at = new_definition
  `dsb_cursor_at p (index:int) <=>
     dsb_minimum p <= index /\ index <= dsb_maximum p`;;

let dsb_same_frame = new_definition
  `dsb_same_frame newer older <=>
     LENGTH (dsb_data newer) = LENGTH (dsb_data older) /\
     dsb_offset newer = dsb_offset older /\
     dsb_minimum newer = dsb_minimum older /\
     dsb_maximum newer = dsb_maximum older /\
     dsb_writable newer = dsb_writable older /\
     dsb_zone newer = dsb_zone older`;;

let dsb_shifted_by = new_definition
  `dsb_shifted_by shifted base (amount:int) <=>
     dsb_offset shifted = dsb_offset base + amount /\
     dsb_plength shifted = dsb_plength base /\
     dsb_pelts shifted = dsb_pelts base /\
     dsb_data shifted = dsb_data base /\
     dsb_minimum shifted = dsb_minimum base /\
     dsb_maximum shifted = dsb_maximum base /\
     dsb_zone shifted = dsb_zone base /\
     dsb_writable shifted = dsb_writable base`;;

let dsb_same_state_shape = new_definition
  `dsb_same_state_shape newer older <=>
     LENGTH (dsb_data newer) = LENGTH (dsb_data older) /\
     dsb_offset newer = dsb_offset older /\
     dsb_minimum newer = dsb_minimum older /\
     dsb_maximum newer = dsb_maximum older /\
     dsb_writable newer = dsb_writable older /\
     dsb_zone newer = dsb_zone older`;;

let dsb_alias_through = new_definition
  `dsb_alias_through view backing old_view <=>
     dsb_data view = dsb_data backing /\
     LENGTH (dsb_data backing) = LENGTH (dsb_data old_view) /\
     dsb_offset view = dsb_offset old_view /\
     dsb_minimum view = dsb_minimum old_view /\
     dsb_maximum view = dsb_maximum old_view /\
     dsb_writable view = dsb_writable old_view /\
     dsb_zone view = dsb_zone old_view`;;

let dsb_copy_of = new_definition
  `dsb_copy_of (copied:int64 list) (source:int64 list) <=>
     LENGTH copied = LENGTH source /\
     !i:int.
       (&0:int) <= i /\ i < &(LENGTH copied)
       ==> EL (num_of_int i) copied = EL (num_of_int i) source`;;

let dsb_update = new_definition
  `dsb_update (f:int->A) (index:int) (value:A) =
     \query. if query = index then value else f query`;;

let dsb_stored_at = new_definition
  `dsb_stored_at newer older (index:int) (limb:int64) <=>
     dsb_same_frame newer older /\
     dsb_pelts newer = dsb_update (dsb_pelts older) index limb /\
     dsb_pelts newer index = limb`;;

let dsb_value_map_from = new_definition
  `dsb_value_map_from (m:int->int64) (index:int) (count:int) =
     if count <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int count - 1)
         (\k. dsb_radix pow k * dsb_u64 (m (index + &k)))`;;

let dsb_value_at = new_definition
  `dsb_value_at p (index:int) (size:int) =
     dsb_value_map_from (dsb_pelts p) index size`;;

let dsb_value = new_definition
  `dsb_value p (size:int) =
     dsb_value_at p (dsb_offset p) size`;;

let dsb_value_sub = new_definition
  `dsb_value_sub (m:int->int64) (lower:int) (upper:int) =
     dsb_value_map_from m lower (upper - lower)`;;

let dsb_normalized = new_definition
  `dsb_normalized p (size:int32) <=>
     dsb_valid p (ival size) /\
     (&9223372036854775808:int) <=
       dsb_u64 (dsb_pelts p (dsb_offset p + ival size - (&1:int)))`;;

let dsb_reciprocal_3by2 = new_definition
  `dsb_reciprocal_3by2 (v:int64) (dh:int64) (dl:int64) <=>
     dsb_u64 v =
       ((dsb_radix * dsb_radix * dsb_radix - (&1:int)) div
        (dsb_u64 dl + dsb_radix * dsb_u64 dh)) - dsb_radix`;;

let dsb_word_flag64 = new_definition
  `dsb_word_flag64 (limb:int64) (constant:int64) (flag:bool) <=>
     (dsb_u64 limb = dsb_u64 constant ==> flag = T) /\
     (flag = T ==> limb = constant)`;;

let dsb_and_word_flag64 = new_definition
  `dsb_and_word_flag64
     (first:int64) (first_constant:int64)
     (second:int64) (second_constant:int64) (result:bool) <=>
     ?first_flag:bool.
       dsb_word_flag64 first first_constant first_flag /\
       (if first_flag
        then dsb_word_flag64 second second_constant result
        else result = F)`;;

let dsb_compare_int = new_definition
  `dsb_compare_int (a:int) (b:int) =
     if a < b then --(&1:int) else if b < a then (&1:int) else (&0:int)`;;

let dsb_carry_bounds = new_definition
  `dsb_carry_bounds (carry:int64) <=>
     (&0:int) <= dsb_u64 carry /\ dsb_u64 carry <= (&1:int)`;;

let dsb_submul_effect = new_definition
  `dsb_submul_effect
     (newer:dsb_ptr) (older:dsb_ptr) (start:int)
     (divisor:dsb_ptr) (size:int)
                     (factor:int64) (borrow:int64) <=>
     dsb_value_at newer start size -
       dsb_ipow dsb_radix size * dsb_u64 borrow =
     dsb_value_at older start size -
       dsb_value divisor size * dsb_u64 factor /\
     (!j:int.
       j < start \/ start + size <= j
       ==> dsb_pelts newer j = dsb_pelts older j)`;;

let dsb_add_effect = new_definition
  `dsb_add_effect
     (newer:dsb_ptr) (older:dsb_ptr) (start:int)
     (addend:dsb_ptr) (size:int)
                  (carry:int64) <=>
     dsb_carry_bounds carry /\
     dsb_value_at newer start size +
       dsb_ipow dsb_radix size * dsb_u64 carry =
     dsb_value_at older start size + dsb_value addend size /\
     (!j:int.
       j < start \/ start + size <= j
       ==> dsb_pelts newer j = dsb_pelts older j)`;;

let dsb_div3by2_result = new_definition
  `dsb_div3by2_result
     (qu:int64) (rl:int64) (rh:int64)
     (xh:int64) (xm:int64) (xl:int64)
     (dh:int64) (dl:int64) (v:int64) <=>
     dsb_reciprocal_3by2 v dh dl /\
     dsb_u64 qu * dsb_u64 dl +
       dsb_radix * dsb_u64 qu * dsb_u64 dh +
       (dsb_u64 rl + dsb_radix * dsb_u64 rh) =
     dsb_u64 xl + dsb_radix * dsb_u64 xm +
       dsb_radix * dsb_radix * dsb_u64 xh /\
     (&0:int) <= dsb_u64 rl + dsb_radix * dsb_u64 rh /\
     dsb_u64 rl + dsb_radix * dsb_u64 rh <
       dsb_u64 dl + dsb_radix * dsb_u64 dh`;;

let dsb_loop_invariant = new_definition
  `dsb_loop_invariant
     (sx:int32) (sy:int32) (i:int32) (mdn:int32)
     (original_x:dsb_ptr) (original_q:dsb_ptr)
     (x_state:dsb_ptr) (q_state:dsb_ptr) (xp:dsb_ptr) (qp:dsb_ptr)
     (qh:int64) (x1:int64) (dh:int64) (dl:int64) (vy:int) <=>
     ((&0:int) <= ival i /\ ival i <= ival sx - ival sy) /\
     dsb_offset qp = dsb_offset q_state + ival i /\
     dsb_offset xp = dsb_offset x_state + ival sy + ival i - (&2:int) /\
     dsb_plength qp = dsb_plength q_state /\
     dsb_minimum qp = dsb_minimum q_state /\
     dsb_maximum qp = dsb_maximum q_state /\
     dsb_plength xp = dsb_plength x_state /\
     dsb_minimum xp = dsb_minimum x_state /\
     dsb_maximum xp = dsb_maximum x_state /\
     dsb_pelts qp = dsb_pelts q_state /\
     dsb_pelts xp = dsb_pelts x_state /\
     dsb_writable qp = T /\ dsb_writable xp = T /\
     dsb_value original_x (ival sx) =
       (dsb_value qp (ival sx - ival sy - ival i) +
        dsb_u64 qh * dsb_ipow dsb_radix (ival sx - ival sy - ival i)) *
       vy * dsb_ipow dsb_radix (ival i) +
       dsb_value x_state (ival sy + ival i - (&1:int)) +
       dsb_ipow dsb_radix (ival sy + ival i - (&1:int)) * dsb_u64 x1 /\
     dsb_value_sub (dsb_pelts x_state)
       (dsb_offset xp + ival mdn)
       (dsb_offset xp + ival mdn + ival sy - (&1:int)) +
       dsb_ipow dsb_radix (ival sy - (&1:int)) * dsb_u64 x1 < vy /\
     dsb_u64 (dsb_pelts x_state (dsb_offset xp)) +
       dsb_radix * dsb_u64 x1 <= dsb_u64 dl + dsb_radix * dsb_u64 dh`;;

let dsb_final_post = new_definition
  `dsb_final_post
     (sx:int32) (sy:int32)
     (original_x:dsb_ptr) (divisor:dsb_ptr)
     (quotient:dsb_ptr) (remainder:dsb_ptr) (qh:int64) <=>
     dsb_value original_x (ival sx) =
       (dsb_value quotient (ival sx - ival sy) +
        dsb_ipow dsb_radix (ival sx - ival sy) * dsb_u64 qh) *
       dsb_value divisor (ival sy) +
       dsb_value remainder (ival sy) /\
     dsb_value remainder (ival sy) < dsb_value divisor (ival sy) /\
     dsb_carry_bounds qh`;;

let dsb_quotient_write = new_definition
  `dsb_quotient_write
     (sx:int32) (sy:int32) (old_i:int32) (next_i:int32) (mdn:int32)
     (original_x:dsb_ptr) (original_q:dsb_ptr)
     (x_state:dsb_ptr) (q_state:dsb_ptr) (xp:dsb_ptr) (qp:dsb_ptr)
     (qh:int64) (x1:int64) (dh:int64) (dl:int64) (vy:int)
     (quotient:int64) <=>
     dsb_cursor_at qp (dsb_offset qp - (&1:int)) /\
     !q_shift:dsb_ptr.
       dsb_shifted_by q_shift qp (--(&1:int))
       ==>
       let lower = dsb_offset q_shift + (&1:int) in
       let upper =
         dsb_offset q_shift + (ival sx - ival sy - ival next_i) in
       let index = dsb_offset q_shift in
       let old = dsb_pelts q_state in
       (lower <= upper /\ (index < lower \/ upper <= index)) /\
       (dsb_value_sub old lower upper =
          dsb_value_sub (dsb_update old index quotient) lower upper
        ==>
        dsb_access_at q_shift index /\ dsb_writable q_shift = T /\
        (!stored_q next_q:dsb_ptr.
          dsb_alias_through stored_q next_q q_shift /\
          dsb_alias_through stored_q next_q q_shift /\
          dsb_same_state_shape next_q q_state /\
          dsb_pelts stored_q =
            dsb_update (dsb_pelts q_shift) (dsb_offset stored_q) quotient
          ==>
          ival next_i < ival old_i /\
          dsb_loop_invariant sx sy next_i mdn original_x original_q
            x_state next_q xp stored_q qh x1 dh dl vy))`;;

let dsb_correction_branch = new_definition
  `dsb_correction_branch
     (sx:int32) (sy:int32) (old_i:int32) (next_i:int32) (mdn:int32)
     (original_x:dsb_ptr) (base_x:dsb_ptr)
     (original_q:dsb_ptr) (divisor:dsb_ptr)
     (x_state:dsb_ptr) (q_state:dsb_ptr)
     (xp:dsb_ptr) (qp:dsb_ptr) (xd:dsb_ptr)
     (qh:int64) (qu:int64) (old_high:int64)
     (dh:int64) (dl:int64) (vy:int) <=>
     (&0:int) < dsb_u64 qu /\
     ((&0:int) < dsb_u64 qu
      ==>
      dsb_ipow dsb_radix (ival sy) - vy <=
        dsb_value xd (ival sy - (&1:int)) +
        dsb_ipow dsb_radix (ival sy - (&1:int)) * dsb_u64 old_high /\
      (dsb_ipow dsb_radix (ival sy) - vy <=
         dsb_value xd (ival sy - (&1:int)) +
         dsb_ipow dsb_radix (ival sy - (&1:int)) * dsb_u64 old_high
       ==>
       !xc1:int64 list.
         dsb_copy_of xc1 (dsb_data x_state)
         ==>
         dsb_int32_in_bounds (ival sy - (&1:int)) /\
         (!add_size:int32.
           ival add_size = ival sy - (&1:int)
           ==>
           dsb_valid xd (ival add_size) /\
           dsb_valid divisor (ival add_size) /\
           dsb_writable xd = T /\
           (!xd4 xp4 x5:dsb_ptr.
             dsb_alias_through xd4 x5 xd /\
             dsb_alias_through xp4 x5 xp /\
             dsb_same_state_shape x5 x_state
             ==>
             !carry:int64.
               dsb_add_effect xd4 xd (dsb_offset xd) divisor
                 (ival add_size) carry
               ==>
               dsb_value x5 (ival next_i) = dsb_value x_state (ival next_i) /\
               (dsb_value x5 (ival next_i) =
                  dsb_value x_state (ival next_i)
                ==>
                ~(dsb_radix = (&0:int)) /\
                (!dh_plus_carry:int64.
                  dsb_u64 dh_plus_carry =
                    (dsb_u64 dh + dsb_u64 carry) rem dsb_radix
                  ==>
                  !new_high:int64.
                    dsb_u64 new_high =
                      (dsb_u64 old_high + dsb_u64 dh_plus_carry)
                      rem dsb_radix
                    ==>
                    dsb_value xd4 (ival sy - (&1:int)) +
                      dsb_ipow dsb_radix (ival sy - (&1:int)) *
                        dsb_u64 new_high =
                    dsb_value xd (ival sy - (&1:int)) +
                      dsb_ipow dsb_radix (ival sy - (&1:int)) *
                        dsb_u64 old_high +
                      vy - dsb_ipow dsb_radix (ival sy)) /\
                (!new_high:int64.
                  dsb_value xd4 (ival sy - (&1:int)) +
                    dsb_ipow dsb_radix (ival sy - (&1:int)) *
                      dsb_u64 new_high =
                  dsb_value xd (ival sy - (&1:int)) +
                    dsb_ipow dsb_radix (ival sy - (&1:int)) *
                      dsb_u64 old_high +
                    vy - dsb_ipow dsb_radix (ival sy)
                  ==>
                  dsb_uint64_in_bounds (dsb_u64 qu - (&1:int)) /\
                  (!corrected_qu:int64.
                    dsb_u64 corrected_qu = dsb_u64 qu - (&1:int)
                    ==>
                    dsb_quotient_write sx sy old_i next_i mdn
                      original_x original_q x5 q_state xp4 qp
                      qh new_high dh dl vy corrected_qu)))))))`;;

let dsb_small_after_estimate = new_definition
  `dsb_small_after_estimate
     (sx:int32) (sy:int32) (old_i:int32) (next_i:int32) (mdn:int32)
     (original_x:dsb_ptr) (base_x:dsb_ptr)
     (original_q:dsb_ptr) (divisor:dsb_ptr)
     (x_state:dsb_ptr) (q_state:dsb_ptr)
     (xp:dsb_ptr) (qp:dsb_ptr) (xd:dsb_ptr)
     (qh:int64) (old_x1:int64) (dh:int64) (dl:int64) (vy:int)
     (qu:int64) (rl:int64) (rh:int64) <=>
     let lower = dsb_offset x_state in
     let middle = dsb_offset xd in
     let upper =
       dsb_offset x_state + ival sy + ival old_i - (&1:int) in
     let m = dsb_pelts x_state in
     (lower <= middle /\ middle <= upper) /\
     (dsb_value_sub m lower upper =
        dsb_value_sub m lower middle +
        dsb_value_sub m middle upper *
          dsb_ipow dsb_radix (middle - lower)
      ==>
      !xc:int64 list.
        dsb_copy_of xc (dsb_data x_state)
        ==>
        dsb_int32_in_bounds (ival sy - (&2:int)) /\
        (!sub_size:int32.
          ival sub_size = ival sy - (&2:int)
          ==>
          dsb_valid divisor (ival sub_size) /\
          dsb_valid xd (ival sub_size) /\
          dsb_writable xd = T /\
          (!xd2 xp2 x3:dsb_ptr.
            dsb_alias_through xd2 x3 xd /\
            dsb_alias_through xp2 x3 xp /\
            dsb_same_state_shape x3 x_state
            ==>
            !cy:int64.
              dsb_submul_effect xd2 xd (dsb_offset xd) divisor
                (ival sub_size) qu cy
              ==>
              dsb_value x3 (ival next_i) = dsb_value x_state (ival next_i) /\
              (dsb_value x3 (ival next_i) =
                 dsb_value x_state (ival next_i)
               ==>
               !cy1:int64.
                 (if dsb_u64 rl < dsb_u64 cy
                  then cy1 = (word 1:int64)
                  else cy1 = (word 0:int64))
                 ==>
                 !new_low:int64.
                   dsb_u64 new_low =
                     (dsb_u64 rl - dsb_u64 cy) rem dsb_radix
                   ==>
                   !cy2:int64.
                     (if dsb_u64 rh < dsb_u64 cy1
                      then cy2 = (word 1:int64)
                      else cy2 = (word 0:int64))
                     ==>
                     !new_high:int64.
                       dsb_u64 new_high =
                         (dsb_u64 rh - dsb_u64 cy1) rem dsb_radix
                       ==>
                       let update_index = dsb_offset xp2 in
                       let old = dsb_pelts x3 in
                       let updated = dsb_update old update_index new_low in
                       let xd_upper =
                         dsb_offset xd2 + ival sy - (&1:int) in
                       let prefix_upper =
                         dsb_offset x3 + ival next_i in
                       let short_upper =
                         dsb_offset xd2 + ival sy - (&2:int) in
                       (dsb_offset xd2 <= update_index /\
                        update_index < xd_upper) /\
                       dsb_value_sub updated (dsb_offset xd2) xd_upper =
                         dsb_value_sub old (dsb_offset xd2) xd_upper +
                         (dsb_u64 new_low - dsb_u64 (old update_index)) *
                           dsb_ipow dsb_radix
                             (update_index - dsb_offset xd2) /\
                       (dsb_offset x3 <= prefix_upper /\
                        (update_index < dsb_offset x3 \/
                         prefix_upper <= update_index)) /\
                       dsb_value_sub old (dsb_offset x3) prefix_upper =
                         dsb_value_sub updated
                           (dsb_offset x3) prefix_upper /\
                       (dsb_offset xd2 <= short_upper /\
                        (update_index < dsb_offset xd2 \/
                         short_upper <= update_index)) /\
                       dsb_value_sub old (dsb_offset xd2) short_upper =
                         dsb_value_sub updated
                           (dsb_offset xd2) short_upper /\
                       dsb_access_at xp2 update_index /\
                       dsb_writable xp2 = T /\
                       (!xd3 xp3 x4:dsb_ptr.
                         dsb_alias_through xp3 x4 xp2 /\
                         dsb_alias_through xd3 x4 xd2 /\
                         dsb_alias_through xp3 x4 xp2 /\
                         dsb_same_state_shape x4 x3 /\
                         dsb_pelts xp3 =
                           dsb_update (dsb_pelts xp2)
                             (dsb_offset xp3) new_low
                         ==>
                         let relation =
                           dsb_value xd3 (ival sy - (&1:int)) +
                             dsb_ipow dsb_radix (ival sy - (&1:int)) *
                               dsb_u64 new_high -
                             dsb_ipow dsb_radix (ival sy) * dsb_u64 cy2 =
                           dsb_value xd (ival sy) +
                             dsb_ipow dsb_radix (ival sy) * dsb_u64 old_x1 -
                             dsb_u64 qu * vy in
                         relation /\
                         (relation
                          ==>
                          !zero_carry:bool.
                            dsb_word_flag64 cy2 (word 0:int64) zero_carry
                            ==>
                            if zero_carry
                            then
                              dsb_quotient_write sx sy old_i next_i mdn
                                original_x original_q x4 q_state xp3 qp
                                qh new_high dh dl vy qu
                            else
                              dsb_correction_branch
                                sx sy old_i next_i mdn
                                original_x base_x original_q divisor
                                x4 q_state xp3 qp xd3
                                qh qu new_high dh dl vy))))))`;;

let dsb_max_quotient_branch = new_definition
  `dsb_max_quotient_branch
     (sx:int32) (sy:int32) (old_i:int32) (next_i:int32) (mdn:int32)
     (original_x:dsb_ptr) (base_x:dsb_ptr)
     (original_q:dsb_ptr) (divisor:dsb_ptr)
     (x_state:dsb_ptr) (q_state:dsb_ptr)
     (xp:dsb_ptr) (qp:dsb_ptr) (xd:dsb_ptr)
     (qh:int64) (dh:int64) (dl:int64) (vy:int) <=>
     let estimate =
       dsb_value_sub (dsb_pelts xd)
         (dsb_offset xd + (&1:int))
         (dsb_offset xd + ival sy - (&1:int)) +
       dsb_ipow dsb_radix (ival sy - (&2:int)) * dsb_u64 dl +
       dsb_ipow dsb_radix (ival sy - (&1:int)) * dsb_u64 dh < vy in
     estimate /\
     (estimate
      ==>
      !xc:int64 list.
        dsb_copy_of xc (dsb_data x_state)
        ==>
        dsb_valid divisor (ival sy) /\
        dsb_valid xd (ival sy) /\
        dsb_writable xd = T /\
        (!xd2 xp2 x3:dsb_ptr.
          dsb_alias_through xd2 x3 xd /\
          dsb_alias_through xp2 x3 xp /\
          dsb_same_state_shape x3 x_state
          ==>
          !borrow:int64.
            dsb_submul_effect xd2 xd (dsb_offset xd) divisor
              (ival sy) (word 18446744073709551615:int64) borrow
            ==>
            dsb_value x3 (ival next_i) = dsb_value x_state (ival next_i) /\
            (dsb_value x3 (ival next_i) =
               dsb_value x_state (ival next_i)
             ==>
             let lower = dsb_offset x3 in
             let middle = dsb_offset xd2 in
             let upper =
               dsb_offset x3 + ival sy + ival next_i - (&1:int) in
             let m = dsb_pelts x3 in
             (lower <= middle /\ middle <= upper) /\
             (dsb_value_sub m lower upper =
                dsb_value_sub m lower middle +
                dsb_value_sub m middle upper *
                  dsb_ipow dsb_radix (middle - lower)
              ==>
              dsb_quotient_write sx sy old_i next_i mdn
                original_x original_q x3 q_state xp2 qp qh
                (dsb_pelts xp2 (dsb_offset xp2 + (&1:int)))
                dh dl vy (word 18446744073709551615:int64)))))`;;

let dsb_small_quotient_branch = new_definition
  `dsb_small_quotient_branch
     (sx:int32) (sy:int32) (old_i:int32) (next_i:int32) (mdn:int32)
     (original_x:dsb_ptr) (base_x:dsb_ptr)
     (original_q:dsb_ptr) (divisor:dsb_ptr)
     (x_state:dsb_ptr) (q_state:dsb_ptr)
     (xp:dsb_ptr) (qp:dsb_ptr) (xd:dsb_ptr)
     (qh:int64) (old_x1:int64) (dh:int64) (dl:int64) (v:int64) (vy:int)
     (nx0:int64) <=>
     dsb_u64 nx0 + dsb_radix * dsb_u64 old_x1 <
       dsb_u64 dl + dsb_radix * dsb_u64 dh /\
     dsb_access_at xp (dsb_offset xp) /\
     dsb_access_at xp (dsb_offset xp + (&1:int)) /\
     let xp0 = dsb_pelts xp (dsb_offset xp) in
     let xp1 = dsb_pelts xp (dsb_offset xp + (&1:int)) in
     let vlx = dsb_value xd (ival sy - (&2:int)) in
     let decomposition =
       dsb_value xd (ival sy) =
         vlx +
         dsb_ipow dsb_radix (ival sy - (&2:int)) *
           (dsb_u64 xp0 + dsb_radix * dsb_u64 xp1) in
     decomposition /\
     (decomposition
      ==>
      (&9223372036854775808:int) <= dsb_u64 dh /\
      dsb_reciprocal_3by2 v dh dl /\
      dsb_u64 xp1 + dsb_radix * dsb_u64 old_x1 <
        dsb_u64 dl + dsb_radix * dsb_u64 dh /\
      (!qu rl rh:int64.
        dsb_div3by2_result qu rl rh old_x1 xp1 xp0 dh dl v
        ==>
        dsb_small_after_estimate sx sy old_i next_i mdn
          original_x base_x original_q divisor
          x_state q_state xp qp xd qh old_x1 dh dl vy qu rl rh))`;;

let dsb_loop_exit = new_definition
  `dsb_loop_exit
     (sx:int32) (sy:int32) (i:int32)
     (original_x:dsb_ptr) (divisor:dsb_ptr)
     (x_state:dsb_ptr) (q_state:dsb_ptr) (xp:dsb_ptr)
     (qh:int64) (x1:int64) <=>
     let lower = dsb_offset x_state in
     let upper = dsb_offset xp in
     let index = dsb_offset xp + (&1:int) in
     let old = dsb_pelts x_state in
     (lower <= upper /\ (index < lower \/ upper <= index)) /\
     (dsb_value_sub old lower upper =
        dsb_value_sub (dsb_update old index x1) lower upper
      ==>
      dsb_access_at xp index /\ dsb_writable xp = T /\
      (!stored_view stored_state:dsb_ptr.
        dsb_alias_through stored_view stored_state xp /\
        dsb_same_state_shape stored_state x_state /\
        dsb_pelts stored_view = dsb_update (dsb_pelts xp) index x1 /\
        dsb_pelts stored_view index = x1
        ==>
        dsb_final_post sx sy original_x divisor q_state stored_state qh))`;;

let dsb_loop_body = new_definition
  `dsb_loop_body
     (sx:int32) (sy:int32) (i:int32) (mdn:int32)
     (original_x:dsb_ptr) (base_x:dsb_ptr)
     (original_q:dsb_ptr) (divisor:dsb_ptr)
     (x_state:dsb_ptr) (q_state:dsb_ptr) (xp:dsb_ptr) (qp:dsb_ptr)
     (qh:int64) (x1:int64) (dh:int64) (dl:int64) (v:int64) (vy:int) <=>
     dsb_int32_in_bounds (ival i - (&1:int)) /\
     (!next_i:int32.
       ival next_i = ival i - (&1:int)
       ==>
       dsb_cursor_at xp (dsb_offset xp - (&1:int)) /\
       (!xp_shift:dsb_ptr.
         dsb_shifted_by xp_shift xp (--(&1:int))
         ==>
         dsb_cursor_at xp_shift (dsb_offset xp_shift + ival mdn) /\
         (!xd:dsb_ptr.
           dsb_shifted_by xd xp_shift (ival mdn)
           ==>
           dsb_access_at xp_shift (dsb_offset xp_shift + (&1:int)) /\
           let nx0 = dsb_pelts xp_shift (dsb_offset xp_shift + (&1:int)) in
           !max_case:bool.
             dsb_and_word_flag64 x1 dh nx0 dl max_case
             ==>
             if max_case
             then
               dsb_max_quotient_branch sx sy i next_i mdn
                 original_x base_x original_q divisor
                 x_state q_state xp_shift qp xd qh dh dl vy
             else
               dsb_small_quotient_branch sx sy i next_i mdn
                 original_x base_x original_q divisor
                 x_state q_state xp_shift qp xd
                 qh x1 dh dl v vy nx0)))`;;

let dsb_all_loop_states = new_definition
  `dsb_all_loop_states
     (sx:int32) (sy:int32) (mdn:int32)
     (original_x:dsb_ptr) (base_x:dsb_ptr)
     (original_q:dsb_ptr) (divisor:dsb_ptr)
     (qh:int64) (dh:int64) (dl:int64) (v:int64) (vy:int) <=>
     !x1:int64. !i:int32. !qp xp x_state q_state:dsb_ptr.
       dsb_same_state_shape x_state base_x /\
       dsb_same_state_shape q_state original_q /\
       dsb_loop_invariant sx sy i mdn original_x original_q
         x_state q_state xp qp qh x1 dh dl vy
       ==>
       if (&0:int) < ival i
       then
         dsb_loop_body sx sy i mdn original_x base_x original_q divisor
           x_state q_state xp qp qh x1 dh dl v vy
       else
         dsb_loop_exit sx sy i original_x divisor
           x_state q_state xp qh x1`;;

let dsb_loop_start_with_divisor = new_definition
  `dsb_loop_start_with_divisor
     (sx:int32) (sy:int32) (i:int32) (mdn:int32)
     (original_x:dsb_ptr) (base_x:dsb_ptr)
     (original_q:dsb_ptr) (divisor:dsb_ptr)
     (x_state:dsb_ptr) (q_state:dsb_ptr) (xp:dsb_ptr) (qp:dsb_ptr)
     (qh:int64) (x1:int64) (dh:int64) (dl:int64) (v:int64) (vy:int) <=>
     dsb_loop_invariant sx sy i mdn original_x original_q
       x_state q_state xp qp qh x1 dh dl vy /\
     dsb_all_loop_states sx sy mdn original_x base_x original_q divisor
       qh dh dl v vy`;;

let dsb_pre_adjust = new_definition
  `dsb_pre_adjust
     (sx:int32) (sy:int32) (i:int32) (mdn:int32)
     (original_x:dsb_ptr) (divisor:dsb_ptr) (initial_q:dsb_ptr)
     (xp:dsb_ptr) (qp:dsb_ptr) (xd:dsb_ptr)
     (qh:int64) (dh:int64) (dl:int64) (v:int64) (vy:int) <=>
     !zero_flag:bool.
       dsb_word_flag64 qh (word 0:int64) zero_flag
       ==>
       (zero_flag = F
        ==>
        (&0:int) <= ival sy /\
        dsb_valid xd (ival sy) /\
        dsb_valid divisor (ival sy) /\
        dsb_writable xd = T) /\
       (!x_state xp_state:dsb_ptr.
         (?branch_flag:bool.
           dsb_word_flag64 qh (word 0:int64) branch_flag /\
           (if branch_flag
            then x_state = original_x /\ xp_state = xp
            else
              ?xd_state:dsb_ptr.
                dsb_alias_through xd_state x_state xd /\
                dsb_alias_through xp_state x_state xp /\
                dsb_same_state_shape x_state original_x /\
                (?borrow:int64.
                  dsb_submul_effect xd_state xd (dsb_offset xd) divisor
                    (ival sy) (word 1:int64) borrow)))
         ==>
         dsb_access_at xp_state (dsb_offset xp_state + (&1:int)) /\
         dsb_loop_start_with_divisor sx sy i mdn
           original_x x_state initial_q divisor
           x_state initial_q xp_state qp qh
           (dsb_pelts xp_state (dsb_offset xp_state + (&1:int)))
           dh dl v vy)`;;

let dsb_initial_setup = new_definition
  `dsb_initial_setup
     (sy:int32) (sx:int32) (x:dsb_ptr) (y:dsb_ptr) (q:dsb_ptr) <=>
     dsb_int32_in_bounds (ival sx - (&2:int)) /\
     (!xp_amount:int32.
       ival xp_amount = ival sx - (&2:int)
       ==>
       dsb_cursor_at x (dsb_offset x + ival xp_amount) /\
       (!xp:dsb_ptr.
         dsb_shifted_by xp x (ival xp_amount)
         ==>
         dsb_int32_in_bounds (ival sx - ival sy) /\
         (!i:int32.
           ival i = ival sx - ival sy
           ==>
           dsb_cursor_at q (dsb_offset q + ival i) /\
           (!qp:dsb_ptr.
             dsb_shifted_by qp q (ival i)
             ==>
             dsb_int32_in_bounds (ival sy - (&1:int)) /\
             (!high_index:int32.
               ival high_index = ival sy - (&1:int)
               ==>
               dsb_access_at y (dsb_offset y + ival high_index) /\
               let dh = dsb_pelts y (dsb_offset y + ival high_index) in
               dsb_int32_in_bounds (ival sy - (&2:int)) /\
               (!low_index:int32.
                 ival low_index = ival sy - (&2:int)
                 ==>
                 dsb_access_at y (dsb_offset y + ival low_index) /\
                 let dl =
                   dsb_pelts y (dsb_offset y + ival low_index) in
                 (&9223372036854775808:int) <= dsb_u64 dh /\
                 (!v:int64.
                   dsb_reciprocal_3by2 v dh dl
                   ==>
                   dsb_int32_in_bounds (ival sx - ival sy) /\
                   (!i_again:int32.
                     ival i_again = ival sx - ival sy
                     ==>
                     dsb_int32_in_bounds ((&2:int) - ival sy) /\
                     (!mdn:int32.
                       ival mdn = (&2:int) - ival sy
                       ==>
                       dsb_cursor_at xp (dsb_offset xp + ival mdn) /\
                       (!xd:dsb_ptr.
                         dsb_shifted_by xd xp (ival mdn)
                         ==>
                         let vy = dsb_value y (ival sy) in
                         dsb_valid xd (ival sy) /\
                         dsb_valid y (ival sy) /\
                         (!r:int32.
                           ival r =
                             dsb_compare_int
                               (dsb_value xd (ival sy))
                               (dsb_value y (ival sy))
                           ==>
                           !qh:int64.
                             (if (&0:int) <= ival r
                              then qh = (word 1:int64)
                              else qh = (word 0:int64))
                             ==>
                             dsb_pre_adjust sx sy i_again mdn
                               x y q xp qp xd qh dh dl v vy)))))))))))`;;

let statement =
  `!sy:int32. !sx:int32.
   !x y q:dsb_ptr.
     (&3:int) <= ival sy /\
     ival sy <= ival sx /\
     dsb_valid x (ival sx) /\
     dsb_valid y (ival sy) /\
     dsb_valid q (ival sx - ival sy) /\
     dsb_writable q = T /\
     dsb_writable x = T /\
     dsb_normalized y sy
     ==>
     dsb_initial_setup sy sx x y q`;;

Format.pp_print_flush Format.std_formatter ();;
Format.pp_set_formatter_out_channel Format.std_formatter stdout;;
close_out dsb_output;;

(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/div_Div_wmpn_divrem_1qtvc: the verification condition
  for one-limb multiprecision division, including divisor normalization,
  reciprocal division, quotient-array updates, loop invariants, and the final
  quotient/remainder relation. This file contains no proof.
*)

let ddr1_output = open_out "/dev/null";;
Format.pp_set_formatter_out_channel Format.std_formatter ddr1_output;;

needs "Library/words.ml";;
needs "Library/isum.ml";;

new_type_abbrev
  ("ddr1_ptr",`:(num#(int->int64))#(int#(int#(int#(bool#Z))))`);;

let ddr1_radix = new_definition
  `ddr1_radix = (&18446744073709551616:int)`;;

let ddr1_u64 = new_definition
  `ddr1_u64 (x:int64) = (&(val x):int)`;;

let ddr1_int32_in_bounds = new_definition
  `ddr1_int32_in_bounds (x:int) <=>
     --(&2147483648:int) <= x /\ x <= (&2147483647:int)`;;

let ddr1_uint64_in_bounds = new_definition
  `ddr1_uint64_in_bounds (x:int) <=>
     (&0:int) <= x /\ x <= (&18446744073709551615:int)`;;

let ddr1_ipow = new_definition
  `ddr1_ipow (base:int) (exponent:int) =
     base pow (if exponent < (&0:int) then 0 else num_of_int exponent)`;;

let ddr1_data = new_definition
  `ddr1_data (p:ddr1_ptr) = FST p`;;

let ddr1_offset = new_definition
  `ddr1_offset (p:ddr1_ptr) = FST (SND p)`;;

let ddr1_minimum = new_definition
  `ddr1_minimum (p:ddr1_ptr) = FST (SND (SND p))`;;

let ddr1_maximum = new_definition
  `ddr1_maximum (p:ddr1_ptr) = FST (SND (SND (SND p)))`;;

let ddr1_writable = new_definition
  `ddr1_writable (p:ddr1_ptr) =
     FST (SND (SND (SND (SND p))))`;;

let ddr1_zone = new_definition
  `ddr1_zone (p:ddr1_ptr) =
     SND (SND (SND (SND (SND p))))`;;

let ddr1_pelts = new_definition
  `ddr1_pelts (p:ddr1_ptr) = SND (ddr1_data p)`;;

let ddr1_plength = new_definition
  `ddr1_plength p = (&(FST (ddr1_data p)):int)`;;

let ddr1_valid = new_definition
  `ddr1_valid p (size:int) <=>
     ddr1_int32_in_bounds size /\
     (&0:int) <= size /\
     (&0:int) <= ddr1_minimum p /\
     ddr1_minimum p <= ddr1_offset p /\
     ddr1_offset p + size <= ddr1_maximum p /\
     ddr1_maximum p <= ddr1_plength p`;;

let ddr1_access_at = new_definition
  `ddr1_access_at p (index:int) <=>
     ddr1_minimum p <= ddr1_offset p + index /\
     ddr1_offset p + index < ddr1_maximum p`;;

let ddr1_same_frame = new_definition
  `ddr1_same_frame newer older <=>
     FST (ddr1_data newer) = FST (ddr1_data older) /\
     ddr1_offset newer = ddr1_offset older /\
     ddr1_minimum newer = ddr1_minimum older /\
     ddr1_maximum newer = ddr1_maximum older /\
     ddr1_writable newer = ddr1_writable older /\
     ddr1_zone newer = ddr1_zone older`;;

let ddr1_update = new_definition
  `ddr1_update (f:int->A) (index:int) (value:A) =
     \query. if query = index then value else f query`;;

let ddr1_value_map_from = new_definition
  `ddr1_value_map_from (m:int->int64) (index:int) (count:int) =
     if count <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int count - 1)
         (\k. ddr1_radix pow k * ddr1_u64 (m (index + &k)))`;;

let ddr1_value_sub = new_definition
  `ddr1_value_sub (m:int->int64) (lower:int) (upper:int) =
     ddr1_value_map_from m lower (upper - lower)`;;

let ddr1_value = new_definition
  `ddr1_value p (size:int) =
     ddr1_value_sub
       (ddr1_pelts p) (ddr1_offset p) (ddr1_offset p + size)`;;

let ddr1_reciprocal = new_definition
  `ddr1_reciprocal (v:int64) (d:int64) <=>
     ddr1_u64 v =
       ((ddr1_radix * ddr1_radix - (&1:int)) div ddr1_u64 d) -
       ddr1_radix`;;

let ddr1_index_bounds = new_definition
  `ddr1_index_bounds (i:int32) (msb:int32) <=>
     --(&1:int) <= ival i /\ ival i <= ival msb`;;

let ddr1_normalized_initial = new_definition
  `ddr1_normalized_initial
     (mult:int) x q (sz:int32) (msb:int32) (ry:int64) <=>
     ddr1_index_bounds msb msb /\
     (&0:int) < ddr1_u64 ry /\
     mult *
       ddr1_value_sub (ddr1_pelts x)
         (ddr1_offset x + ival msb + (&1:int))
         (ddr1_offset x + ival sz) =
       ddr1_value_sub (ddr1_pelts q)
         (ddr1_offset q + ival msb + (&1:int))
         (ddr1_offset q + ival sz) * ddr1_u64 ry + (&0:int) /\
     (&0:int) <= ddr1_radix - mult /\
     (&0:int) rem mult = (&0:int)`;;

let ddr1_normalized_invariant = new_definition
  `ddr1_normalized_invariant
     (mult:int) x q (sz:int32) (msb:int32)
     (ry:int64) (r:int64) (i:int32) <=>
     ddr1_index_bounds i msb /\
     ddr1_u64 r < ddr1_u64 ry /\
     mult *
       ddr1_value_sub (ddr1_pelts x)
         (ddr1_offset x + ival i + (&1:int))
         (ddr1_offset x + ival sz) =
       ddr1_value_sub (ddr1_pelts q)
         (ddr1_offset q + ival i + (&1:int))
         (ddr1_offset q + ival sz) * ddr1_u64 ry + ddr1_u64 r /\
     ddr1_u64 r <= ddr1_radix - mult /\
     ddr1_u64 r rem mult = (&0:int)`;;

let ddr1_plain_initial = new_definition
  `ddr1_plain_initial x q (sz:int32) (msb:int32) (y:int64) <=>
     ddr1_index_bounds msb msb /\
     (&0:int) < ddr1_u64 y /\
     ddr1_value_sub (ddr1_pelts x)
       (ddr1_offset x + ival msb + (&1:int))
       (ddr1_offset x + ival sz) =
       ddr1_value_sub (ddr1_pelts q)
         (ddr1_offset q + ival msb + (&1:int))
         (ddr1_offset q + ival sz) * ddr1_u64 y + (&0:int)`;;

let ddr1_plain_invariant = new_definition
  `ddr1_plain_invariant
     x q (sz:int32) (msb:int32) (y:int64) (r:int64) (i:int32) <=>
     ddr1_index_bounds i msb /\
     ddr1_u64 r < ddr1_u64 y /\
     ddr1_value_sub (ddr1_pelts x)
       (ddr1_offset x + ival i + (&1:int))
       (ddr1_offset x + ival sz) =
       ddr1_value_sub (ddr1_pelts q)
         (ddr1_offset q + ival i + (&1:int))
         (ddr1_offset q + ival sz) * ddr1_u64 y + ddr1_u64 r`;;

let ddr1_normalized_after_store = new_definition
  `ddr1_normalized_after_store
     (mult:int) x q (sz:int32) (msb:int32)
     (ry:int64) (remainder:int64) (i:int32) <=>
     ddr1_int32_in_bounds (ival i - (&1:int)) /\
     (!next:int32.
        ival next = ival i - (&1:int)
        ==>
        ival next < ival i /\
        ddr1_index_bounds next msb /\
        ddr1_u64 remainder < ddr1_u64 ry /\
        mult *
          ddr1_value_sub (ddr1_pelts x)
            (ddr1_offset x + ival next + (&1:int))
            (ddr1_offset x + ival sz) =
          ddr1_value_sub (ddr1_pelts q)
            (ddr1_offset q + ival next + (&1:int))
            (ddr1_offset q + ival sz) * ddr1_u64 ry +
          ddr1_u64 remainder /\
        ddr1_u64 remainder <= ddr1_radix - mult /\
        ddr1_u64 remainder rem mult = (&0:int))`;;

let ddr1_plain_after_store = new_definition
  `ddr1_plain_after_store
     x q (sz:int32) (msb:int32)
     (y:int64) (remainder:int64) (i:int32) <=>
     ddr1_int32_in_bounds (ival i - (&1:int)) /\
     (!next:int32.
        ival next = ival i - (&1:int)
        ==>
        ival next < ival i /\
        ddr1_index_bounds next msb /\
        ddr1_u64 remainder < ddr1_u64 y /\
        ddr1_value_sub (ddr1_pelts x)
          (ddr1_offset x + ival next + (&1:int))
          (ddr1_offset x + ival sz) =
          ddr1_value_sub (ddr1_pelts q)
            (ddr1_offset q + ival next + (&1:int))
            (ddr1_offset q + ival sz) * ddr1_u64 y +
          ddr1_u64 remainder)`;;

let ddr1_normalized_store = new_definition
  `ddr1_normalized_store
     (mult:int) x q1 (sz:int32) (msb:int32)
     (ry:int64) (remainder:int64) (i:int32) (quotient:int64) <=>
     !q2:ddr1_ptr.
       ddr1_same_frame q2 q1
       ==>
       ddr1_pelts q2 =
         ddr1_update (ddr1_pelts q1)
           (ddr1_offset q2 + ival i) quotient /\
       ddr1_pelts q2 (ddr1_offset q2 + ival i) = quotient
       ==>
       ddr1_normalized_after_store
         mult x q2 sz msb ry remainder i`;;

let ddr1_plain_store = new_definition
  `ddr1_plain_store
     x q1 (sz:int32) (msb:int32)
     (y:int64) (remainder:int64) (i:int32) (quotient:int64) <=>
     !q2:ddr1_ptr.
       ddr1_same_frame q2 q1
       ==>
       ddr1_pelts q2 =
         ddr1_update (ddr1_pelts q1)
           (ddr1_offset q2 + ival i) quotient /\
       ddr1_pelts q2 (ddr1_offset q2 + ival i) = quotient
       ==>
       ddr1_plain_after_store x q2 sz msb y remainder i`;;

let ddr1_normalized_value_update = new_definition
  `ddr1_normalized_value_update
     (mult:int) x q1 (sz:int32) (msb:int32)
     (ry:int64) (remainder:int64) (i:int32) (quotient:int64) <=>
     let upper = ddr1_offset q1 + ival sz in
     let middle = ddr1_offset q1 + (&1:int) + ival i in
     let index = ddr1_offset q1 + ival i in
     let old = ddr1_pelts q1 in
     (middle <= upper /\ (index < middle \/ upper <= index)) /\
     (ddr1_value_sub old middle upper =
        ddr1_value_sub (ddr1_update old index quotient) middle upper
      ==>
      ddr1_access_at q1 (ival i) /\
      ddr1_writable q1 = T /\
      ddr1_normalized_store
        mult x q1 sz msb ry remainder i quotient)`;;

let ddr1_plain_value_update = new_definition
  `ddr1_plain_value_update
     x q1 (sz:int32) (msb:int32)
     (y:int64) (remainder:int64) (i:int32) (quotient:int64) <=>
     let upper = ddr1_offset q1 + ival sz in
     let middle = ddr1_offset q1 + (&1:int) + ival i in
     let index = ddr1_offset q1 + ival i in
     let old = ddr1_pelts q1 in
     (middle <= upper /\ (index < middle \/ upper <= index)) /\
     (ddr1_value_sub old middle upper =
        ddr1_value_sub (ddr1_update old index quotient) middle upper
      ==>
      ddr1_access_at q1 (ival i) /\
      ddr1_writable q1 = T /\
      ddr1_plain_store x q1 sz msb y remainder i quotient)`;;

let ddr1_normalized_division_step = new_definition
  `ddr1_normalized_division_step
     (mult:int) x q1 (sz:int32) (msb:int32)
     (ry:int64) (i:int32) (low:int64) (combined:int64) <=>
     !quotient remainder:int64.
       ddr1_u64 quotient * ddr1_u64 ry + ddr1_u64 remainder =
         ddr1_u64 low + ddr1_radix * ddr1_u64 combined /\
       (&0:int) <= ddr1_u64 remainder /\
       ddr1_u64 remainder < ddr1_u64 ry
       ==>
       ~(mult = (&0:int)) /\
       ddr1_normalized_value_update
         mult x q1 sz msb ry remainder i quotient`;;

let ddr1_plain_division_step = new_definition
  `ddr1_plain_division_step
     x q1 (sz:int32) (msb:int32)
     (y:int64) (r:int64) (i:int32) <=>
     !quotient remainder:int64.
       ddr1_u64 quotient * ddr1_u64 y + ddr1_u64 remainder =
         ddr1_u64 (ddr1_pelts x (ddr1_offset x + ival i)) +
         ddr1_radix * ddr1_u64 r /\
       (&0:int) <= ddr1_u64 remainder /\
       ddr1_u64 remainder < ddr1_u64 y
       ==>
       ddr1_plain_value_update
         x q1 sz msb y remainder i quotient`;;

let ddr1_normalized_combined = new_definition
  `ddr1_normalized_combined
     (mult:int) x q1 (sz:int32) (msb:int32) (i:int32)
     (ry:int64) (v:int64) (r:int64) (low:int64) (high:int64) <=>
     !combined:int64.
       ddr1_u64 combined = ddr1_u64 r + ddr1_u64 high
       ==>
       (ddr1_radix div (&2:int) <= ddr1_u64 ry /\
        ddr1_u64 combined < ddr1_u64 ry /\
        ddr1_reciprocal v ry) /\
       ddr1_normalized_division_step
         mult x q1 sz msb ry i low combined`;;

let ddr1_normalized_shifted_limb = new_definition
  `ddr1_normalized_shifted_limb
     (mult:int) x q1 (sz:int32) (msb:int32) (i:int32)
     (ry:int64) (v:int64) (r:int64) (shift:int64) <=>
     !low high:int64.
       ddr1_u64 low + ddr1_radix * ddr1_u64 high =
         ddr1_ipow (&2:int) (ddr1_u64 shift) *
         ddr1_u64 (ddr1_pelts x (ddr1_offset x + ival i)) /\
       ddr1_u64 low rem ddr1_ipow (&2:int) (ddr1_u64 shift) =
         (&0:int) /\
       ddr1_u64 low <=
         ddr1_radix - ddr1_ipow (&2:int) (ddr1_u64 shift) /\
       ddr1_u64 high < ddr1_ipow (&2:int) (ddr1_u64 shift)
       ==>
       ddr1_uint64_in_bounds (ddr1_u64 r + ddr1_u64 high) /\
       ddr1_normalized_combined
         mult x q1 sz msb i ry v r low high`;;

let ddr1_normalized_iteration = new_definition
  `ddr1_normalized_iteration
     (mult:int) x q1 (sz:int32) (msb:int32) (clz:int32)
     (i:int32) (ry:int64) (v:int64) (r:int64) <=>
     ddr1_access_at x (ival i) /\
     (&0:int) <= ival clz /\
     (!shift:int64.
        ddr1_u64 shift = ival clz
        ==>
        ((&0:int) < ddr1_u64 shift /\
         ddr1_u64 shift < (&64:int)) /\
        ddr1_normalized_shifted_limb
          mult x q1 sz msb i ry v r shift)`;;

let ddr1_normalized_finish = new_definition
  `ddr1_normalized_finish
     x q1 (sz:int32) (clz:int32) (y:int64) (r:int64) <=>
     (&0:int) <= ival clz /\
     (!shift:int64.
        ddr1_u64 shift = ival clz
        ==>
        (((&0:int) <= ddr1_u64 shift /\
          ddr1_u64 shift < (&64:int)) /\
         ddr1_u64 r rem ddr1_ipow (&2:int) (ddr1_u64 shift) =
           (&0:int)) /\
        (!res:int64.
           ddr1_u64 r =
             ddr1_ipow (&2:int) (ddr1_u64 shift) * ddr1_u64 res
           ==>
           (&0:int) <= ival clz /\
           (!shift_again:int64.
              ddr1_u64 shift_again = ival clz
              ==>
              (((&0:int) <= ddr1_u64 shift_again /\
                ddr1_u64 shift_again < (&64:int)) /\
               ddr1_u64 r rem
                 ddr1_ipow (&2:int) (ddr1_u64 shift_again) =
                 (&0:int)) /\
              (!result:int64.
                 ddr1_u64 r =
                   ddr1_ipow (&2:int) (ddr1_u64 shift_again) *
                   ddr1_u64 result
                 ==>
                 ddr1_value x (ival sz) =
                   ddr1_value q1 (ival sz) * ddr1_u64 y +
                   ddr1_u64 result /\
                 ddr1_u64 result < ddr1_u64 y))))`;;

let ddr1_normalized_loop_body = new_definition
  `ddr1_normalized_loop_body
     (mult:int) x q1 (sz:int32) (msb:int32) (clz:int32)
     (y:int64) (ry:int64) (v:int64) (r:int64) (i:int32) <=>
     if (&0:int) <= ival i then
       ddr1_normalized_iteration mult x q1 sz msb clz i ry v r
     else
       ddr1_normalized_finish x q1 sz clz y r`;;

let ddr1_normalized_all_loops = new_definition
  `ddr1_normalized_all_loops
     (mult:int) x q (sz:int32) (msb:int32) (clz:int32)
     (y:int64) (ry:int64) (v:int64) <=>
     !r:int64. !i:int32. !q1:ddr1_ptr.
       ddr1_same_frame q1 q
       ==>
       ddr1_normalized_invariant mult x q1 sz msb ry r i
       ==>
       ddr1_normalized_loop_body
         mult x q1 sz msb clz y ry v r i`;;

let ddr1_normalized_reciprocal = new_definition
  `ddr1_normalized_reciprocal
     (mult:int) x q (sz:int32) (msb:int32) (clz:int32)
     (y:int64) (ry:int64) <=>
     !v:int64.
       ddr1_reciprocal v ry
       ==>
       ddr1_normalized_initial mult x q sz msb ry /\
       ddr1_normalized_all_loops mult x q sz msb clz y ry v`;;

let ddr1_normalized_divisor = new_definition
  `ddr1_normalized_divisor
     (mult:int) x q (sz:int32) (msb:int32) (clz:int32)
     (y:int64) (shift:int64) <=>
     !ry:int64.
       ddr1_u64 ry =
         ddr1_ipow (&2:int) (ddr1_u64 shift) * ddr1_u64 y
       ==>
       ddr1_radix div (&2:int) <= ddr1_u64 ry /\
       ddr1_normalized_reciprocal mult x q sz msb clz y ry`;;

let ddr1_normalized_branch = new_definition
  `ddr1_normalized_branch
     x q (sz:int32) (msb:int32) (clz:int32) (y:int64) <=>
     let mult = ddr1_ipow (&2:int) (ival clz) in
     (&0:int) <= ival clz /\
     (!shift:int64.
        ddr1_u64 shift = ival clz
        ==>
        (((&0:int) <= ddr1_u64 shift /\
          ddr1_u64 shift < (&64:int)) /\
         ddr1_ipow (&2:int) (ddr1_u64 shift) * ddr1_u64 y <=
           (&18446744073709551615:int)) /\
        ddr1_normalized_divisor mult x q sz msb clz y shift)`;;

let ddr1_plain_iteration = new_definition
  `ddr1_plain_iteration
     x q1 (sz:int32) (msb:int32)
     (y:int64) (v:int64) (r:int64) (i:int32) <=>
     ddr1_access_at x (ival i) /\
     (ddr1_radix div (&2:int) <= ddr1_u64 y /\
      ddr1_u64 r < ddr1_u64 y /\
      ddr1_reciprocal v y) /\
     ddr1_plain_division_step x q1 sz msb y r i`;;

let ddr1_plain_finish = new_definition
  `ddr1_plain_finish x q1 (sz:int32) (y:int64) (r:int64) <=>
     ddr1_value x (ival sz) =
       ddr1_value q1 (ival sz) * ddr1_u64 y + ddr1_u64 r /\
     ddr1_u64 r < ddr1_u64 y`;;

let ddr1_plain_loop_body = new_definition
  `ddr1_plain_loop_body
     x q1 (sz:int32) (msb:int32)
     (y:int64) (v:int64) (r:int64) (i:int32) <=>
     if (&0:int) <= ival i then
       ddr1_plain_iteration x q1 sz msb y v r i
     else
       ddr1_plain_finish x q1 sz y r`;;

let ddr1_plain_all_loops = new_definition
  `ddr1_plain_all_loops
     x q (sz:int32) (msb:int32) (y:int64) (v:int64) <=>
     !r:int64. !i:int32. !q1:ddr1_ptr.
       ddr1_same_frame q1 q
       ==>
       ddr1_plain_invariant x q1 sz msb y r i
       ==>
       ddr1_plain_loop_body x q1 sz msb y v r i`;;

let ddr1_plain_branch = new_definition
  `ddr1_plain_branch
     x q (sz:int32) (msb:int32) (y:int64) <=>
     ddr1_radix div (&2:int) <= ddr1_u64 y /\
     (!v:int64.
        ddr1_reciprocal v y
        ==>
        ddr1_plain_initial x q sz msb y /\
        ddr1_plain_all_loops x q sz msb y v)`;;

let ddr1_clz_premise = new_definition
  `ddr1_clz_premise (clz:int32) (y:int64) <=>
     ddr1_ipow (&2:int) (ival clz) * ddr1_u64 y <=
       (&18446744073709551615:int) /\
     (&18446744073709551615:int) <
       (&2:int) * ddr1_ipow (&2:int) (ival clz) * ddr1_u64 y /\
     (&0:int) <= ival clz /\
     ival clz < (&64:int)`;;

let ddr1_after_msb = new_definition
  `ddr1_after_msb
     x q (sz:int32) (msb:int32) (y:int64) <=>
     (&0:int) < ddr1_u64 y /\
     (!clz:int32.
        ddr1_clz_premise clz y
        ==>
        if (&0:int) < ival clz then
          ddr1_normalized_branch x q sz msb clz y
        else
          ddr1_plain_branch x q sz msb y)`;;

let statement =
  `!x:ddr1_ptr. !sz:int32. !q:ddr1_ptr. !y:int64.
     ddr1_valid x (ival sz) /\
     ddr1_valid q (ival sz) /\
     ddr1_writable q = T /\
     (&0:int) < ival sz /\
     (&0:int) < ddr1_u64 y
     ==>
     ddr1_int32_in_bounds (ival sz - (&1:int)) /\
     (!msb:int32.
        ival msb = ival sz - (&1:int)
        ==>
        ddr1_after_msb x q sz msb y)`;;

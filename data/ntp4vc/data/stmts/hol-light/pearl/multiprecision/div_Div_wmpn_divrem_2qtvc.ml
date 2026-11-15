(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/div_Div_wmpn_divrem_2qtvc: the verification condition
  for two-limb multiprecision division, including reciprocal division,
  quotient storage, remainder storage, and loop-invariant preservation. This
  file contains no proof.
*)

let ddr2_output = open_out "/dev/null";;
Format.pp_set_formatter_out_channel Format.std_formatter ddr2_output;;

needs "Library/words.ml";;
needs "Library/isum.ml";;

new_type_abbrev
  ("ddr2_ptr",`:(num#(int->int64))#(int#(int#(int#(bool#Z))))`);;

let ddr2_radix = new_definition
  `ddr2_radix = (&18446744073709551616:int)`;;

let ddr2_u64 = new_definition
  `ddr2_u64 (x:int64) = (&(val x):int)`;;

let ddr2_int32_in_bounds = new_definition
  `ddr2_int32_in_bounds (x:int) <=>
     --(&2147483648:int) <= x /\ x <= (&2147483647:int)`;;

let ddr2_ipow = new_definition
  `ddr2_ipow (base:int) (exponent:int) =
     base pow (if exponent < (&0:int) then 0 else num_of_int exponent)`;;

let ddr2_data = new_definition
  `ddr2_data (p:ddr2_ptr) = FST p`;;

let ddr2_offset = new_definition
  `ddr2_offset (p:ddr2_ptr) = FST (SND p)`;;

let ddr2_minimum = new_definition
  `ddr2_minimum (p:ddr2_ptr) = FST (SND (SND p))`;;

let ddr2_maximum = new_definition
  `ddr2_maximum (p:ddr2_ptr) = FST (SND (SND (SND p)))`;;

let ddr2_writable = new_definition
  `ddr2_writable (p:ddr2_ptr) =
     FST (SND (SND (SND (SND p))))`;;

let ddr2_zone = new_definition
  `ddr2_zone (p:ddr2_ptr) =
     SND (SND (SND (SND (SND p))))`;;

let ddr2_pelts = new_definition
  `ddr2_pelts (p:ddr2_ptr) = SND (ddr2_data p)`;;

let ddr2_plength = new_definition
  `ddr2_plength p = (&(FST (ddr2_data p)):int)`;;

let ddr2_valid = new_definition
  `ddr2_valid p (size:int) <=>
     ddr2_int32_in_bounds size /\
     (&0:int) <= size /\
     (&0:int) <= ddr2_minimum p /\
     ddr2_minimum p <= ddr2_offset p /\
     ddr2_offset p + size <= ddr2_maximum p /\
     ddr2_maximum p <= ddr2_plength p`;;

let ddr2_bounds = new_definition
  `ddr2_bounds p (displacement:int) <=>
     ddr2_minimum p <= ddr2_offset p + displacement /\
     ddr2_offset p + displacement < ddr2_maximum p`;;

let ddr2_inclusive_bounds = new_definition
  `ddr2_inclusive_bounds p (displacement:int) <=>
     ddr2_minimum p <= ddr2_offset p + displacement /\
     ddr2_offset p + displacement <= ddr2_maximum p`;;

let ddr2_same_shape = new_definition
  `ddr2_same_shape newer older <=>
     FST (ddr2_data newer) = FST (ddr2_data older) /\
     ddr2_offset newer = ddr2_offset older /\
     ddr2_minimum newer = ddr2_minimum older /\
     ddr2_maximum newer = ddr2_maximum older /\
     ddr2_writable newer = ddr2_writable older /\
     ddr2_zone newer = ddr2_zone older`;;

let ddr2_shift_copy = new_definition
  `ddr2_shift_copy shifted base (displacement:int) <=>
     ddr2_offset shifted = ddr2_offset base + displacement /\
     ddr2_plength shifted = ddr2_plength base /\
     ddr2_pelts shifted = ddr2_pelts base /\
     ddr2_data shifted = ddr2_data base /\
     ddr2_minimum shifted = ddr2_minimum base /\
     ddr2_maximum shifted = ddr2_maximum base /\
     ddr2_zone shifted = ddr2_zone base /\
     ddr2_writable shifted = ddr2_writable base`;;

let ddr2_update = new_definition
  `ddr2_update (f:int->A) (index:int) (value:A) =
     \query. if query = index then value else f query`;;

let ddr2_value_map_from = new_definition
  `ddr2_value_map_from (m:int->int64) (index:int) (count:int) =
     if count <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int count - 1)
         (\k. ddr2_radix pow k * ddr2_u64 (m (index + &k)))`;;

let ddr2_value_sub = new_definition
  `ddr2_value_sub (m:int->int64) (lower:int) (upper:int) =
     ddr2_value_map_from m lower (upper - lower)`;;

let ddr2_value = new_definition
  `ddr2_value p (size:int) =
     ddr2_value_sub
       (ddr2_pelts p) (ddr2_offset p) (ddr2_offset p + size)`;;

let ddr2_reciprocal_3by2 = new_definition
  `ddr2_reciprocal_3by2 (dinv:int64) (dh:int64) (dl:int64) <=>
     ddr2_u64 dinv =
       (ddr2_radix * ddr2_radix * ddr2_radix - (&1:int)) div
         (ddr2_u64 dl + ddr2_radix * ddr2_u64 dh) -
       ddr2_radix`;;

let ddr2_remainder = new_definition
  `ddr2_remainder
     (low:int64) (high:int64) (dl:int64) (dh:int64) <=>
     ddr2_u64 low + ddr2_radix * ddr2_u64 high <
     ddr2_u64 dl + ddr2_radix * ddr2_u64 dh`;;

let ddr2_loop_state = new_definition
  `ddr2_loop_state
     (sx:int32) (x:ddr2_ptr) (y:ddr2_ptr) (qstate:ddr2_ptr)
     (qh:int64) (low:int64) (high:int64)
     (work:ddr2_ptr) (index:int) <=>
     (&0:int) <= index /\
     index <= ival sx - (&2:int) /\
     ddr2_offset work = ddr2_offset x + index /\
     ddr2_plength work = ddr2_plength x /\
     ddr2_minimum work = ddr2_minimum x /\
     ddr2_maximum work = ddr2_maximum x /\
     ddr2_pelts work = ddr2_pelts x /\
     ddr2_writable work = T /\
     ddr2_value x (ival sx) =
       (ddr2_value_sub
          (ddr2_pelts qstate)
          (ddr2_offset qstate + index)
          (ddr2_offset qstate + ival sx - (&2:int)) +
        ddr2_u64 qh *
          ddr2_ipow ddr2_radix (ival sx - (&2:int) - index)) *
         ddr2_value y (&2:int) *
         ddr2_ipow ddr2_radix index +
       ddr2_value x index +
       ddr2_ipow ddr2_radix index *
         (ddr2_u64 low + ddr2_radix * ddr2_u64 high) /\
     ddr2_remainder low high
       (ddr2_pelts y (ddr2_offset y))
       (ddr2_pelts y (ddr2_offset y + (&1:int)))`;;

let ddr2_adjust_test = new_definition
  `ddr2_adjust_test
     (dh:int64) (dl:int64) (o3:int64) (o4:int64) =
     if ddr2_u64 dh <= ddr2_u64 o3 then
       if ddr2_u64 dh < ddr2_u64 o3 then T
       else if ddr2_u64 dl <= ddr2_u64 o4 then T else F
     else F`;;

let ddr2_borrow_all = new_definition
  `ddr2_borrow_all (o4:int64) (dl:int64) <=>
     !r0 b:int64.
       ddr2_u64 r0 - ddr2_radix * ddr2_u64 b =
           ddr2_u64 o4 - ddr2_u64 dl - (&0:int) /\
       (&0:int) <= ddr2_u64 b /\
       ddr2_u64 b <= (&1:int)
       ==>
       (&0:int) <= ddr2_u64 b /\
       ddr2_u64 b <= (&1:int)`;;

let ddr2_adjust_true_witness = new_definition
  `ddr2_adjust_true_witness
     (rh:int64) (rl:int64) (qh:int64)
     (dh:int64) (dl:int64) (o3:int64) (o4:int64) <=>
     ?d d1:int64.
       (ddr2_u64 rl - ddr2_radix * ddr2_u64 d =
          ddr2_u64 o4 - ddr2_u64 dl - (&0:int) /\
        (&0:int) <= ddr2_u64 d /\
        ddr2_u64 d <= (&1:int)) /\
       (ddr2_u64 rh - ddr2_radix * ddr2_u64 d1 =
          ddr2_u64 o3 - ddr2_u64 dh - ddr2_u64 d /\
        (&0:int) <= ddr2_u64 d1 /\
        ddr2_u64 d1 <= (&1:int)) /\
       qh = (word 1:int64)`;;

let ddr2_initial_adjust_witness = new_definition
  `ddr2_initial_adjust_witness
     (rh:int64) (rl:int64) (qh:int64)
     (dh:int64) (dl:int64) (o3:int64) (o4:int64) <=>
     ?selected:bool.
       selected = ddr2_adjust_test dh dl o3 o4 /\
       if selected = T then
         ddr2_adjust_true_witness rh rl qh dh dl o3 o4
       else
         (rh = o3 /\ rl = o4) /\ qh = (word 0:int64)`;;

let ddr2_final_result = new_definition
  `ddr2_final_result
     (sx:int32) (x:ddr2_ptr) (y:ddr2_ptr) (qh:int64)
     (qstate:ddr2_ptr) (result_state:ddr2_ptr) <=>
     ddr2_value x (ival sx) =
       (ddr2_value qstate (ival sx - (&2:int)) +
        ddr2_ipow ddr2_radix (ival sx - (&2:int)) * ddr2_u64 qh) *
         ddr2_value y (&2:int) +
       ddr2_value result_state (&2:int) /\
     ddr2_value result_state (&2:int) < ddr2_value y (&2:int) /\
     (&0:int) <= ddr2_u64 qh /\
     ddr2_u64 qh <= (&1:int)`;;

let ddr2_final_x2_all = new_definition
  `ddr2_final_x2_all
     (sx:int32) (x:ddr2_ptr) (y:ddr2_ptr) (qh:int64)
     (qstate:ddr2_ptr) (x1:ddr2_ptr) (low:int64) <=>
     !x2:ddr2_ptr.
       ddr2_same_shape x2 x1
       ==>
       ddr2_pelts x2 =
         ddr2_update (ddr2_pelts x1) (ddr2_offset x2) low
       ==>
       ddr2_final_result sx x y qh qstate x2`;;

let ddr2_final_x1_all = new_definition
  `ddr2_final_x1_all
     (sx:int32) (x:ddr2_ptr) (y:ddr2_ptr) (qh:int64)
     (qstate:ddr2_ptr) (low:int64) (high:int64) <=>
     !x1:ddr2_ptr.
       ddr2_same_shape x1 x
       ==>
       ddr2_pelts x1 =
         ddr2_update
           (ddr2_pelts x) (ddr2_offset x1 + (&1:int)) high /\
       ddr2_pelts x1 (ddr2_offset x1 + (&1:int)) = high
       ==>
       ddr2_bounds x1 (&0:int) /\
       ddr2_writable x1 = T /\
       ddr2_final_x2_all sx x y qh qstate x1 low`;;

let ddr2_next_q2_all = new_definition
  `ddr2_next_q2_all
     (sx:int32) (x:ddr2_ptr) (y:ddr2_ptr) (qh:int64)
     (q1:ddr2_ptr) (work:ddr2_ptr) (i:int32) (o7:int32)
     (r0:int64) (r1:int64) (quotient:int64) <=>
     !q2:ddr2_ptr.
       ddr2_same_shape q2 q1
       ==>
       ddr2_pelts q2 =
           ddr2_update
             (ddr2_pelts q1)
             (ddr2_offset q2 + ival o7)
             quotient /\
       ddr2_pelts q2 (ddr2_offset q2 + ival o7) = quotient
       ==>
       ival o7 < ival i /\
       ddr2_loop_state sx x y q2 qh r0 r1 work (ival o7)`;;

let ddr2_next_o7_all = new_definition
  `ddr2_next_o7_all
     (sx:int32) (x:ddr2_ptr) (y:ddr2_ptr) (qh:int64)
     (q1:ddr2_ptr) (work:ddr2_ptr) (i:int32)
     (r0:int64) (r1:int64) (quotient:int64) <=>
     ddr2_int32_in_bounds (ival i - (&1:int)) /\
     (!o7:int32.
        ival o7 = ival i - (&1:int)
        ==>
        ddr2_bounds q1 (ival o7) /\
        ddr2_writable q1 = T /\
        ddr2_next_q2_all
          sx x y qh q1 work i o7 r0 r1 quotient)`;;

let ddr2_div_result_all = new_definition
  `ddr2_div_result_all
     (sx:int32) (x:ddr2_ptr) (y:ddr2_ptr) (qh:int64)
     (q1:ddr2_ptr) (work:ddr2_ptr) (i:int32)
     (dh:int64) (dl:int64) (current_low:int64) (current_high:int64) <=>
     !quotient r0 r1:int64.
       ddr2_u64 quotient * ddr2_u64 dl +
           ddr2_radix * ddr2_u64 quotient * ddr2_u64 dh +
           ddr2_u64 r0 + ddr2_radix * ddr2_u64 r1 =
         ddr2_u64 (ddr2_pelts work (ddr2_offset work)) +
           ddr2_radix * ddr2_u64 current_low +
           ddr2_radix * ddr2_radix * ddr2_u64 current_high /\
       (&0:int) <= ddr2_u64 r0 + ddr2_radix * ddr2_u64 r1 /\
       ddr2_u64 r0 + ddr2_radix * ddr2_u64 r1 <
         ddr2_u64 dl + ddr2_radix * ddr2_u64 dh
       ==>
       ddr2_next_o7_all
         sx x y qh q1 work i r0 r1 quotient`;;

let ddr2_shifted_work_all = new_definition
  `ddr2_shifted_work_all
     (sx:int32) (x:ddr2_ptr) (y:ddr2_ptr) (qh:int64)
     (q1:ddr2_ptr) (xp:ddr2_ptr) (i:int32)
     (dinv:int64) (dh:int64) (dl:int64)
     (low:int64) (high:int64) <=>
     !work:ddr2_ptr.
       ddr2_shift_copy work xp (--(&1:int))
       ==>
       ddr2_bounds work (&0:int) /\
       ((ddr2_radix div (&2:int) <= ddr2_u64 dh /\
         ddr2_reciprocal_3by2 dinv dh dl /\
         ddr2_remainder low high dl dh) /\
        ddr2_div_result_all
          sx x y qh q1 work i dh dl low high)`;;

let ddr2_loop_step = new_definition
  `ddr2_loop_step
     (sx:int32) (x:ddr2_ptr) (y:ddr2_ptr) (qh:int64)
     (q1:ddr2_ptr) (xp:ddr2_ptr) (i:int32)
     (dinv:int64) (dh:int64) (dl:int64)
     (low:int64) (high:int64) <=>
     if (&0:int) < ival i then
       ddr2_inclusive_bounds xp (--(&1:int)) /\
       ddr2_shifted_work_all
         sx x y qh q1 xp i dinv dh dl low high
     else
       (ddr2_bounds x (&1:int) /\ ddr2_writable x = T) /\
       ddr2_final_x1_all sx x y qh q1 low high`;;

let ddr2_loop_all = new_definition
  `ddr2_loop_all
     (sx:int32) (x:ddr2_ptr) (y:ddr2_ptr) (q:ddr2_ptr)
     (qh:int64) (dinv:int64) (dh:int64) (dl:int64) <=>
     !i:int32. !low high:int64. !xp q1:ddr2_ptr.
       ddr2_same_shape q1 q
       ==>
       ddr2_loop_state sx x y q1 qh low high xp (ival i)
       ==>
       ddr2_loop_step
         sx x y qh q1 xp i dinv dh dl low high`;;

let ddr2_initial_result_all = new_definition
  `ddr2_initial_result_all
     (sx:int32) (x:ddr2_ptr) (y:ddr2_ptr) (q:ddr2_ptr)
     (work:ddr2_ptr) (index:int32) (dinv:int64)
     (dh:int64) (dl:int64) (o3:int64) (o4:int64) <=>
     !rh rl qh:int64.
       ddr2_initial_adjust_witness rh rl qh dh dl o3 o4
       ==>
       ddr2_loop_state sx x y q qh rl rh work (ival index) /\
       ddr2_loop_all sx x y q qh dinv dh dl`;;

let ddr2_dinv_all = new_definition
  `ddr2_dinv_all
     (sx:int32) (x:ddr2_ptr) (y:ddr2_ptr) (q:ddr2_ptr)
     (work:ddr2_ptr) (index:int32)
     (dh:int64) (dl:int64) (o3:int64) (o4:int64) <=>
     !dinv:int64.
       ddr2_reciprocal_3by2 dinv dh dl
       ==>
       (ddr2_adjust_test dh dl o3 o4 = T
        ==>
        ((&0:int) <= (&0:int) /\ (&0:int) <= (&1:int)) /\
        ddr2_borrow_all o4 dl) /\
       ddr2_initial_result_all
         sx x y q work index dinv dh dl o3 o4`;;

let ddr2_index_all = new_definition
  `ddr2_index_all
     (sx:int32) (x:ddr2_ptr) (y:ddr2_ptr) (q:ddr2_ptr)
     (work:ddr2_ptr)
     (dh:int64) (dl:int64) (o3:int64) (o4:int64) <=>
     !index:int32.
       ival index = ival sx - (&2:int)
       ==>
       ddr2_radix div (&2:int) <= ddr2_u64 dh /\
       ddr2_dinv_all sx x y q work index dh dl o3 o4`;;

let ddr2_loaded_work = new_definition
  `ddr2_loaded_work
     (sx:int32) (x:ddr2_ptr) (y:ddr2_ptr)
     (q:ddr2_ptr) (work:ddr2_ptr) <=>
     let dh = ddr2_pelts y (ddr2_offset y + (&1:int)) in
     let dl = ddr2_pelts y (ddr2_offset y) in
     let o3 = ddr2_pelts work (ddr2_offset work + (&1:int)) in
     let o4 = ddr2_pelts work (ddr2_offset work) in
     ddr2_bounds y (&1:int) /\
     ddr2_bounds y (&0:int) /\
     ddr2_bounds work (&1:int) /\
     ddr2_bounds work (&0:int) /\
     ddr2_int32_in_bounds (ival sx - (&2:int)) /\
     ddr2_index_all sx x y q work dh dl o3 o4`;;

let ddr2_work_all = new_definition
  `ddr2_work_all
     (sx:int32) (x:ddr2_ptr) (y:ddr2_ptr)
     (q:ddr2_ptr) (displacement:int) <=>
     !work:ddr2_ptr.
       ddr2_shift_copy work x displacement
       ==>
       ddr2_loaded_work sx x y q work`;;

let ddr2_displacement_all = new_definition
  `ddr2_displacement_all
     (sx:int32) (x:ddr2_ptr) (y:ddr2_ptr) (q:ddr2_ptr) <=>
     !displacement:int32.
       ival displacement = ival sx - (&2:int)
       ==>
       ddr2_inclusive_bounds x (ival displacement) /\
       ddr2_work_all sx x y q (ival displacement)`;;

let statement =
  `!sx:int32. !x y q:ddr2_ptr.
     (&2:int) <= ival sx /\
     ddr2_valid x (ival sx) /\
     ddr2_valid y (&2:int) /\
     ddr2_valid q (ival sx - (&2:int)) /\
     ddr2_radix div (&2:int) <=
       ddr2_u64 (ddr2_pelts y (ddr2_offset y + (&1:int))) /\
     ddr2_writable q = T /\
     ddr2_writable x = T
     ==>
     ddr2_int32_in_bounds (ival sx - (&2:int)) /\
     ddr2_displacement_all sx x y q`;;

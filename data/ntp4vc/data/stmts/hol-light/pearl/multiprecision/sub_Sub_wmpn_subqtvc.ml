(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_Sub_wmpn_subqtvc: the verification condition for
  unequal-length multiprecision subtraction, including the initial limbwise
  subtraction, borrow propagation, copying of remaining limbs, pointer
  aliasing, map updates, and memory framing. This file contains no proof.
*)

let wmpnsub_statement_output = open_out "/dev/null";;
Format.set_formatter_out_channel wmpnsub_statement_output;;

needs "Library/words.ml";;
needs "Library/isum.ml";;

let wmpnsub_radix = new_definition
  `wmpnsub_radix = (&18446744073709551616:int)`;;

let wmpnsub_u64 = new_definition
  `wmpnsub_u64 (x:int64) = (&(val x):int)`;;

let wmpnsub_int32_in_bounds = new_definition
  `wmpnsub_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let wmpnsub_radix_power = new_definition
  `wmpnsub_radix_power (n:int) =
     wmpnsub_radix pow (if n < (&0:int) then 0 else num_of_int n)`;;

let wmpnsub_value = new_definition
  `wmpnsub_value
     (pelts:'p->int->int64) (offset:'p->int) (p:'p) (n:int) =
     if n <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int n - 1)
         (\k. wmpnsub_radix pow k *
              wmpnsub_u64 (pelts p (offset p + &k)))`;;

let wmpnsub_valid = new_definition
  `wmpnsub_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (n:int) <=>
     wmpnsub_int32_in_bounds n /\
     (&0:int) <= n /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + n <= maximum p /\
     maximum p <= &(data_length p)`;;

let wmpnsub_same_data = new_definition
  `wmpnsub_same_data
     (data_length:'p->num)
     (pelts:'p->int->int64)
     (left:'p) (right:'p) <=>
     data_length left = data_length right /\
     pelts left = pelts right`;;

let wmpnsub_rebased_snapshot = new_definition
  `wmpnsub_rebased_snapshot
     (data_length:'p->num)
     (pelts:'p->int->int64)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (fresh:'p) (shared:'p) (old:'p) <=>
     wmpnsub_same_data data_length pelts fresh shared /\
     data_length shared = data_length old /\
     offset fresh = offset old /\
     minimum fresh = minimum old /\
     maximum fresh = maximum old /\
     writable fresh = writable old /\
     zone fresh = zone old`;;

let wmpnsub_snapshot_metadata = new_definition
  `wmpnsub_snapshot_metadata
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (fresh:'p) (old:'p) <=>
     data_length fresh = data_length old /\
     offset fresh = offset old /\
     minimum fresh = minimum old /\
     maximum fresh = maximum old /\
     writable fresh = writable old /\
     zone fresh = zone old`;;

let wmpnsub_disjoint = new_definition
  `wmpnsub_disjoint
     (offset:'p->int)
     (left:'p) (left_size:int)
     (right:'p) (right_size:int) <=>
     offset left = offset right \/
     offset left + left_size <= offset right \/
     offset right + right_size <= offset left`;;

let wmpnsub_map_eq_sub = new_definition
  `wmpnsub_map_eq_sub
     (pelts:'p->int->int64)
     (left:'p) (right:'p) (lower:int) (upper:int) <=>
     !i:int.
       lower <= i /\ i < upper
       ==> pelts left i = pelts right i`;;

let wmpnsub_frame = new_definition
  `wmpnsub_frame
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (count:int) <=>
     !j:int.
       j < offset new \/ offset new + count <= j
       ==> pelts new j = pelts old j`;;

let wmpnsub_single_update = new_definition
  `wmpnsub_single_update
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (index:int) (value:int64) <=>
     !j:int.
       pelts new j =
       if j = index then value else pelts old j`;;

let wmpnsub_access = new_definition
  `wmpnsub_access
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (index:int) <=>
     minimum p <= index /\ index < maximum p`;;

let wmpnsub_borrow_range = new_definition
  `wmpnsub_borrow_range (borrow:int64) <=>
     (&0:int) <= wmpnsub_u64 borrow /\
     wmpnsub_u64 borrow <= (&1:int)`;;

let wmpnsub_zero_flag = new_definition
  `wmpnsub_zero_flag (limb:int64) (flag:bool) <=>
     (wmpnsub_u64 limb = wmpnsub_u64 (word 0:int64) ==> flag = T) /\
     (flag = T ==> limb = (word 0:int64))`;;

let wmpnsub_value_equation = new_definition
  `wmpnsub_value_equation
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32)
     (current:'p) (x:'p) (y:'p)
     (index:int) (borrow:int64) <=>
     wmpnsub_value pelts offset current index -
       wmpnsub_radix_power index * wmpnsub_u64 borrow =
       wmpnsub_value pelts offset x index -
       wmpnsub_value pelts offset y (ival sy)`;;

let wmpnsub_alias_invariant = new_definition
  `wmpnsub_alias_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (current:'p) (x_current:'p) (y_current:'p)
     (x:'p) (y:'p) <=>
     pelts x_current = pelts current /\
     pelts y_current = pelts current /\
     (offset current = offset x_current \/
      wmpnsub_map_eq_sub
        pelts x_current x (offset x_current)
        (offset x_current + ival sx)) /\
     (offset current = offset y_current \/
      wmpnsub_map_eq_sub
        pelts y_current y (offset y_current)
        (offset y_current + ival sy))`;;

let wmpnsub_initial_postcondition = new_definition
  `wmpnsub_initial_postcondition
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32)
     (r:'p) (x:'p) (y:'p)
     (current:'p) (x_current:'p) (y_current:'p)
     (borrow:int64) <=>
     wmpnsub_value_equation
       offset pelts sy current x y (ival sy) borrow /\
     wmpnsub_borrow_range borrow /\
     wmpnsub_frame offset pelts current r (ival sy) /\
     (offset current = offset x_current \/
      wmpnsub_map_eq_sub
        pelts x_current x (offset x_current)
        (offset x_current + ival sy)) /\
     (offset current = offset y_current \/
      wmpnsub_map_eq_sub
        pelts y_current y (offset y_current)
        (offset y_current + ival sy))`;;

let wmpnsub_final_state = new_definition
  `wmpnsub_final_state
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (current:'p) (x_current:'p) (y_current:'p)
     (borrow:int64) <=>
     wmpnsub_value_equation
       offset pelts sy current x y (ival sx) borrow /\
     wmpnsub_borrow_range borrow /\
     wmpnsub_frame offset pelts current r (ival sx) /\
     (offset current = offset x_current \/
      wmpnsub_map_eq_sub
        pelts x_current x (offset x_current)
        (offset x_current + ival sx)) /\
     (offset current = offset y_current \/
      wmpnsub_map_eq_sub
        pelts y_current y (offset y_current)
        (offset y_current + ival sy))`;;

let wmpnsub_borrow_invariant = new_definition
  `wmpnsub_borrow_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (index:int32) (borrow:int64)
     (current:'p) (x_current:'p) (y_current:'p) <=>
     ival sy <= ival index /\ ival index <= ival sx /\
     wmpnsub_value_equation
       offset pelts sy current x y (ival index) borrow /\
     wmpnsub_frame offset pelts current r (ival index) /\
     wmpnsub_alias_invariant
       offset pelts sy sx current x_current y_current x y /\
     wmpnsub_borrow_range borrow /\
     (index = sx \/ wmpnsub_u64 borrow = (&1:int))`;;

let wmpnsub_copy_invariant = new_definition
  `wmpnsub_copy_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (index:int32) (borrow:int64)
     (current:'p) (x_current:'p) (y_current:'p) <=>
     ival sy <= ival index /\ ival index <= ival sx /\
     (index = sx \/ wmpnsub_u64 borrow = (&0:int)) /\
     wmpnsub_value_equation
       offset pelts sy current x y (ival index) borrow /\
     wmpnsub_frame offset pelts current r (ival index) /\
     wmpnsub_alias_invariant
       offset pelts sy sx current x_current y_current x y /\
     wmpnsub_borrow_range borrow`;;

let wmpnsub_copy_step = new_definition
  `wmpnsub_copy_step
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (index:int32) (borrow:int64)
     (current:'p) (x_current:'p) (y_current:'p) <=>
     if ival index < ival sx then
       wmpnsub_access
         minimum maximum x_current (offset x_current + ival index) /\
       wmpnsub_access minimum maximum x (offset x + ival index) /\
       (wmpnsub_access
          minimum maximum current (offset current + ival index) /\
        writable current = T) /\
       (!y_next x_next r_next:'p.
          wmpnsub_rebased_snapshot
            data_length pelts offset minimum maximum writable zone
            y_next r_next y_current
          ==>
          wmpnsub_rebased_snapshot
            data_length pelts offset minimum maximum writable zone
            x_next r_next x_current
          ==>
          wmpnsub_snapshot_metadata
            data_length offset minimum maximum writable zone
            r_next current
          ==>
          (wmpnsub_single_update
             pelts r_next current (offset r_next + ival index)
             (pelts x_current (offset x_current + ival index)) /\
           pelts r_next (offset r_next + ival index) =
             pelts x_current (offset x_current + ival index))
          ==>
          wmpnsub_int32_in_bounds (ival index + (&1:int)) /\
          (!next:int32.
             ival next = ival index + (&1:int)
             ==>
             ((&0:int) <= ival sx - ival index /\
              ival sx - ival next < ival sx - ival index) /\
             wmpnsub_copy_invariant
               offset pelts sy sx r x y next borrow
               r_next x_next y_next))
     else
       wmpnsub_final_state
         offset pelts sy sx r x y current x_current y_current borrow`;;

let wmpnsub_copy_loop = new_definition
  `wmpnsub_copy_loop
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (borrow:int64)
     (initial:'p) (x_initial:'p) (y_initial:'p) <=>
     !index:int32. !y_current x_current current:'p.
       wmpnsub_rebased_snapshot
         data_length pelts offset minimum maximum writable zone
         y_current current y_initial
       ==>
       wmpnsub_rebased_snapshot
         data_length pelts offset minimum maximum writable zone
         x_current current x_initial
       ==>
       wmpnsub_snapshot_metadata
         data_length offset minimum maximum writable zone current initial
       ==>
       wmpnsub_copy_invariant
         offset pelts sy sx r x y index borrow
         current x_current y_current
       ==>
       wmpnsub_copy_step
         data_length offset minimum maximum writable zone pelts
         sy sx r x y index borrow current x_current y_current`;;

let wmpnsub_copy_phase = new_definition
  `wmpnsub_copy_phase
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (index:int32) (borrow:int64)
     (current:'p) (x_current:'p) (y_current:'p) <=>
     wmpnsub_copy_invariant
       offset pelts sy sx r x y index borrow current x_current y_current /\
     wmpnsub_copy_loop
       data_length offset minimum maximum writable zone pelts
       sy sx r x y borrow current x_current y_current`;;

let wmpnsub_borrow_step = new_definition
  `wmpnsub_borrow_step
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (index:int32) (borrow:int64)
     (current:'p) (x_current:'p) (y_current:'p) <=>
     if ival index < ival sx then
       wmpnsub_access
         minimum maximum x_current (offset x_current + ival index) /\
       wmpnsub_access minimum maximum x (offset x + ival index) /\
       (!result:int64.
          wmpnsub_u64 result =
            (wmpnsub_u64
               (pelts x_current (offset x_current + ival index)) -
             (&1:int)) rem wmpnsub_radix
          ==>
          (wmpnsub_access
             minimum maximum current (offset current + ival index) /\
           writable current = T) /\
          (!y_next x_next r_next:'p.
             wmpnsub_rebased_snapshot
               data_length pelts offset minimum maximum writable zone
               y_next r_next y_current
             ==>
             wmpnsub_rebased_snapshot
               data_length pelts offset minimum maximum writable zone
               x_next r_next x_current
             ==>
             wmpnsub_snapshot_metadata
               data_length offset minimum maximum writable zone
               r_next current
             ==>
             (wmpnsub_single_update
                pelts r_next current (offset r_next + ival index) result /\
              pelts r_next (offset r_next + ival index) = result)
             ==>
             wmpnsub_int32_in_bounds (ival index + (&1:int)) /\
             (!next:int32.
                ival next = ival index + (&1:int)
                ==>
                (!flag:bool.
                   wmpnsub_zero_flag
                     (pelts x_current (offset x_current + ival index))
                     flag
                   ==>
                   if ~(flag = T) then
                     wmpnsub_copy_phase
                       data_length offset minimum maximum writable zone pelts
                       sy sx r x y next (word 0:int64)
                       r_next x_next y_next
                   else
                     ((&0:int) <= ival sx - ival index /\
                      ival sx - ival next < ival sx - ival index) /\
                     wmpnsub_borrow_invariant
                       offset pelts sy sx r x y next borrow
                       r_next x_next y_next))))
     else
       wmpnsub_copy_phase
         data_length offset minimum maximum writable zone pelts
         sy sx r x y index borrow current x_current y_current`;;

let wmpnsub_borrow_loop = new_definition
  `wmpnsub_borrow_loop
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (initial:'p) (x_initial:'p) (y_initial:'p) <=>
     !index:int32. !borrow:int64.
     !y_current x_current current:'p.
       wmpnsub_rebased_snapshot
         data_length pelts offset minimum maximum writable zone
         y_current current y_initial
       ==>
       wmpnsub_rebased_snapshot
         data_length pelts offset minimum maximum writable zone
         x_current current x_initial
       ==>
       wmpnsub_snapshot_metadata
         data_length offset minimum maximum writable zone current initial
       ==>
       wmpnsub_borrow_invariant
         offset pelts sy sx r x y index borrow
         current x_current y_current
       ==>
       wmpnsub_borrow_step
         data_length offset minimum maximum writable zone pelts
         sy sx r x y index borrow current x_current y_current`;;

let wmpnsub_borrow_phase = new_definition
  `wmpnsub_borrow_phase
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (borrow:int64)
     (current:'p) (x_current:'p) (y_current:'p) <=>
     wmpnsub_borrow_invariant
       offset pelts sy sx r x y sy borrow current x_current y_current /\
     wmpnsub_borrow_loop
       data_length offset minimum maximum writable zone pelts
       sy sx r x y current x_current y_current`;;

let wmpnsub_after_initial_flag = new_definition
  `wmpnsub_after_initial_flag
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (borrow:int64) (flag:bool)
     (current:'p) (x_current:'p) (y_current:'p) <=>
     if ~(flag = T) then
       wmpnsub_borrow_phase
         data_length offset minimum maximum writable zone pelts
         sy sx r x y borrow current x_current y_current
     else
       wmpnsub_copy_phase
         data_length offset minimum maximum writable zone pelts
         sy sx r x y sy borrow current x_current y_current`;;

let wmpnsub_after_initial = new_definition
  `wmpnsub_after_initial
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (borrow:int64)
     (current:'p) (x_current:'p) (y_current:'p) <=>
     !flag:bool.
       wmpnsub_zero_flag borrow flag
       ==>
       wmpnsub_after_initial_flag
         data_length offset minimum maximum writable zone pelts
         sy sx r x y borrow flag current x_current y_current`;;

let statement =
  `!data_length:'p->num.
   !offset minimum maximum:'p->int.
   !writable:'p->bool.
   !zone:'p->'z.
   !pelts:'p->int->int64.
   !sy sx:int32. !r x y:'p.
     (&0:int) <= ival sy
     ==>
     ival sy <= ival sx
     ==>
     wmpnsub_valid
       data_length offset minimum maximum r (ival sx)
     ==>
     wmpnsub_valid
       data_length offset minimum maximum x (ival sx)
     ==>
     wmpnsub_valid
       data_length offset minimum maximum y (ival sy)
     ==>
     wmpnsub_disjoint offset r (ival sx) x (ival sx)
     ==>
     wmpnsub_disjoint offset r (ival sx) y (ival sy)
     ==>
     wmpnsub_same_data data_length pelts r x
     ==>
     wmpnsub_same_data data_length pelts x y
     ==>
     writable r = T
     ==>
     (&0:int) <= ival sy /\
     wmpnsub_valid
       data_length offset minimum maximum r (ival sy) /\
     wmpnsub_valid
       data_length offset minimum maximum x (ival sy) /\
     wmpnsub_valid
       data_length offset minimum maximum y (ival sy) /\
     wmpnsub_disjoint offset r (ival sy) x (ival sy) /\
     wmpnsub_disjoint offset r (ival sy) y (ival sy) /\
     wmpnsub_same_data data_length pelts r x /\
     wmpnsub_same_data data_length pelts x y /\
     writable r = T /\
     (!y_current x_current current:'p.
        wmpnsub_rebased_snapshot
          data_length pelts offset minimum maximum writable zone
          y_current current y
        ==>
        wmpnsub_rebased_snapshot
          data_length pelts offset minimum maximum writable zone
          x_current current x
        ==>
        wmpnsub_snapshot_metadata
          data_length offset minimum maximum writable zone current r
        ==>
        (!borrow:int64.
           wmpnsub_initial_postcondition
             offset pelts sy r x y current x_current y_current borrow
           ==>
           wmpnsub_after_initial
             data_length offset minimum maximum writable zone pelts
             sy sx r x y borrow current x_current y_current))`;;

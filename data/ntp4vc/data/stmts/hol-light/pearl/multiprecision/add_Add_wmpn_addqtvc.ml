(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/add_Add_wmpn_addqtvc: the verification condition for
  unequal-length multiprecision addition, including the initial limbwise
  addition, carry propagation, copying of remaining limbs, pointer aliasing,
  map updates, and memory framing. This file contains no proof.
*)

needs "Library/words.ml";;
needs "Library/isum.ml";;

let wmpnadd_radix = new_definition
  `wmpnadd_radix = (&18446744073709551616:int)`;;

let wmpnadd_int32_in_bounds = new_definition
  `wmpnadd_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let wmpnadd_radix_power = new_definition
  `wmpnadd_radix_power (n:int) =
     wmpnadd_radix pow (if n < (&0:int) then 0 else num_of_int n)`;;

let wmpnadd_value = new_definition
  `wmpnadd_value
     (pelts:'p->int->int64) (offset:'p->int) (p:'p) (n:int) =
     if n <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int n - 1)
         (\k. wmpnadd_radix pow k *
              (&(val (pelts p (offset p + &k))):int))`;;

let wmpnadd_valid = new_definition
  `wmpnadd_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (n:int) <=>
     wmpnadd_int32_in_bounds n /\
     (&0:int) <= n /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + n <= maximum p /\
     maximum p <= &(data_length p)`;;

let wmpnadd_same_data = new_definition
  `wmpnadd_same_data
     (data_length:'p->num)
     (pelts:'p->int->int64)
     (left:'p) (right:'p) <=>
     data_length left = data_length right /\
     pelts left = pelts right`;;

let wmpnadd_rebased_snapshot = new_definition
  `wmpnadd_rebased_snapshot
     (data_length:'p->num)
     (pelts:'p->int->int64)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (fresh:'p) (shared:'p) (old:'p) <=>
     wmpnadd_same_data data_length pelts fresh shared /\
     data_length shared = data_length old /\
     offset fresh = offset old /\
     minimum fresh = minimum old /\
     maximum fresh = maximum old /\
     writable fresh = writable old /\
     zone fresh = zone old`;;

let wmpnadd_snapshot_metadata = new_definition
  `wmpnadd_snapshot_metadata
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

let wmpnadd_disjoint = new_definition
  `wmpnadd_disjoint
     (offset:'p->int)
     (left:'p) (left_size:int)
     (right:'p) (right_size:int) <=>
     offset left = offset right \/
     offset left + left_size <= offset right \/
     offset right + right_size <= offset left`;;

let wmpnadd_map_eq_sub = new_definition
  `wmpnadd_map_eq_sub
     (pelts:'p->int->int64)
     (left:'p) (right:'p) (lower:int) (upper:int) <=>
     !i:int.
       lower <= i /\ i < upper
       ==> pelts left i = pelts right i`;;

let wmpnadd_frame = new_definition
  `wmpnadd_frame
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (count:int) <=>
     !j:int.
       j < offset new \/ offset new + count <= j
       ==> pelts new j = pelts old j`;;

let wmpnadd_single_update = new_definition
  `wmpnadd_single_update
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (index:int) (value:int64) <=>
     !j:int.
       pelts new j =
       if j = index then value else pelts old j`;;

let wmpnadd_access = new_definition
  `wmpnadd_access
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (index:int) <=>
     minimum p <= index /\ index < maximum p`;;

let wmpnadd_carry_range = new_definition
  `wmpnadd_carry_range (carry:int64) <=>
     (&0:int) <= (&(val carry):int) /\
     (&(val carry):int) <= (&1:int)`;;

let wmpnadd_zero_flag = new_definition
  `wmpnadd_zero_flag (limb:int64) (flag:bool) <=>
     ((&(val limb):int) = (&(val (word 0:int64)):int) ==> flag = T) /\
     (flag = T ==> limb = (word 0:int64))`;;

let wmpnadd_value_equation = new_definition
  `wmpnadd_value_equation
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32)
     (current:'p) (x:'p) (y:'p)
     (index:int) (carry:int64) <=>
     wmpnadd_value pelts offset current index +
       wmpnadd_radix_power index * (&(val carry):int) =
       wmpnadd_value pelts offset x index +
       wmpnadd_value pelts offset y (ival sy)`;;

let wmpnadd_alias_invariant = new_definition
  `wmpnadd_alias_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (current:'p) (x_current:'p) (y_current:'p)
     (x:'p) (y:'p) <=>
     pelts x_current = pelts current /\
     pelts y_current = pelts current /\
     (offset current = offset x_current \/
      wmpnadd_map_eq_sub
        pelts x_current x (offset x_current)
        (offset x_current + ival sx)) /\
     (offset current = offset y_current \/
      wmpnadd_map_eq_sub
        pelts y_current y (offset y_current)
        (offset y_current + ival sy))`;;

let wmpnadd_initial_postcondition = new_definition
  `wmpnadd_initial_postcondition
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32)
     (r:'p) (x:'p) (y:'p)
     (current:'p) (x_current:'p) (y_current:'p)
     (carry:int64) <=>
     wmpnadd_value_equation
       offset pelts sy current x y (ival sy) carry /\
     wmpnadd_carry_range carry /\
     wmpnadd_frame offset pelts current r (ival sy) /\
     (offset current = offset x_current \/
      wmpnadd_map_eq_sub
        pelts x_current x (offset x_current)
        (offset x_current + ival sy)) /\
     (offset current = offset y_current \/
      wmpnadd_map_eq_sub
        pelts y_current y (offset y_current)
        (offset y_current + ival sy))`;;

let wmpnadd_final_state = new_definition
  `wmpnadd_final_state
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (current:'p) (x_current:'p) (y_current:'p)
     (carry:int64) <=>
     wmpnadd_value_equation
       offset pelts sy current x y (ival sx) carry /\
     wmpnadd_carry_range carry /\
     wmpnadd_frame offset pelts current r (ival sx) /\
     (offset current = offset x_current \/
      wmpnadd_map_eq_sub
        pelts x_current x (offset x_current)
        (offset x_current + ival sx)) /\
     (offset current = offset y_current \/
      wmpnadd_map_eq_sub
        pelts y_current y (offset y_current)
        (offset y_current + ival sy))`;;

let wmpnadd_carry_invariant = new_definition
  `wmpnadd_carry_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (index:int32) (carry:int64)
     (current:'p) (x_current:'p) (y_current:'p) <=>
     ival sy <= ival index /\ ival index <= ival sx /\
     wmpnadd_value_equation
       offset pelts sy current x y (ival index) carry /\
     wmpnadd_frame offset pelts current r (ival index) /\
     wmpnadd_alias_invariant
       offset pelts sy sx current x_current y_current x y /\
     wmpnadd_carry_range carry /\
     (index = sx \/ (&(val carry):int) = (&1:int))`;;

let wmpnadd_copy_invariant = new_definition
  `wmpnadd_copy_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (index:int32) (carry:int64)
     (current:'p) (x_current:'p) (y_current:'p) <=>
     ival sy <= ival index /\ ival index <= ival sx /\
     (index = sx \/ (&(val carry):int) = (&0:int)) /\
     wmpnadd_value_equation
       offset pelts sy current x y (ival index) carry /\
     wmpnadd_frame offset pelts current r (ival index) /\
     wmpnadd_alias_invariant
       offset pelts sy sx current x_current y_current x y /\
     wmpnadd_carry_range carry`;;

let wmpnadd_copy_step = new_definition
  `wmpnadd_copy_step
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (index:int32) (carry:int64)
     (current:'p) (x_current:'p) (y_current:'p) <=>
     if ival index < ival sx then
       wmpnadd_access
         minimum maximum x_current (offset x_current + ival index) /\
       wmpnadd_access minimum maximum x (offset x + ival index) /\
       (wmpnadd_access
          minimum maximum current (offset current + ival index) /\
        writable current = T) /\
       (!y_next x_next r_next:'p.
          wmpnadd_rebased_snapshot
            data_length pelts offset minimum maximum writable zone
            y_next r_next y_current
          ==>
          wmpnadd_rebased_snapshot
            data_length pelts offset minimum maximum writable zone
            x_next r_next x_current
          ==>
          wmpnadd_snapshot_metadata
            data_length offset minimum maximum writable zone
            r_next current
          ==>
          (wmpnadd_single_update
             pelts r_next current (offset r_next + ival index)
             (pelts x_current (offset x_current + ival index)) /\
           pelts r_next (offset r_next + ival index) =
             pelts x_current (offset x_current + ival index))
          ==>
          wmpnadd_int32_in_bounds (ival index + (&1:int)) /\
          (!next:int32.
             ival next = ival index + (&1:int)
             ==>
             ((&0:int) <= ival sx - ival index /\
              ival sx - ival next < ival sx - ival index) /\
             wmpnadd_copy_invariant
               offset pelts sy sx r x y next carry
               r_next x_next y_next))
     else
       wmpnadd_final_state
         offset pelts sy sx r x y current x_current y_current carry`;;

let wmpnadd_copy_loop = new_definition
  `wmpnadd_copy_loop
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (carry:int64)
     (initial:'p) (x_initial:'p) (y_initial:'p) <=>
     !index:int32. !y_current x_current current:'p.
       wmpnadd_rebased_snapshot
         data_length pelts offset minimum maximum writable zone
         y_current current y_initial
       ==>
       wmpnadd_rebased_snapshot
         data_length pelts offset minimum maximum writable zone
         x_current current x_initial
       ==>
       wmpnadd_snapshot_metadata
         data_length offset minimum maximum writable zone current initial
       ==>
       wmpnadd_copy_invariant
         offset pelts sy sx r x y index carry
         current x_current y_current
       ==>
       wmpnadd_copy_step
         data_length offset minimum maximum writable zone pelts
         sy sx r x y index carry current x_current y_current`;;

let wmpnadd_copy_phase = new_definition
  `wmpnadd_copy_phase
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (index:int32) (carry:int64)
     (current:'p) (x_current:'p) (y_current:'p) <=>
     wmpnadd_copy_invariant
       offset pelts sy sx r x y index carry current x_current y_current /\
     wmpnadd_copy_loop
       data_length offset minimum maximum writable zone pelts
       sy sx r x y carry current x_current y_current`;;

let wmpnadd_carry_step = new_definition
  `wmpnadd_carry_step
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (index:int32) (carry:int64)
     (current:'p) (x_current:'p) (y_current:'p) <=>
     if ival index < ival sx then
       wmpnadd_access
         minimum maximum x_current (offset x_current + ival index) /\
       wmpnadd_access minimum maximum x (offset x + ival index) /\
       (!result:int64.
          (&(val result):int) =
            ((&(val
                 (pelts x_current (offset x_current + ival index))):int) +
             (&1:int)) rem wmpnadd_radix
          ==>
          (wmpnadd_access
             minimum maximum current (offset current + ival index) /\
           writable current = T) /\
          (!y_next x_next r_next:'p.
             wmpnadd_rebased_snapshot
               data_length pelts offset minimum maximum writable zone
               y_next r_next y_current
             ==>
             wmpnadd_rebased_snapshot
               data_length pelts offset minimum maximum writable zone
               x_next r_next x_current
             ==>
             wmpnadd_snapshot_metadata
               data_length offset minimum maximum writable zone
               r_next current
             ==>
             (wmpnadd_single_update
                pelts r_next current (offset r_next + ival index) result /\
              pelts r_next (offset r_next + ival index) = result)
             ==>
             wmpnadd_int32_in_bounds (ival index + (&1:int)) /\
             (!next:int32.
                ival next = ival index + (&1:int)
                ==>
                (!flag:bool.
                   wmpnadd_zero_flag result flag
                   ==>
                   if ~(flag = T) then
                     wmpnadd_copy_phase
                       data_length offset minimum maximum writable zone pelts
                       sy sx r x y next (word 0:int64)
                       r_next x_next y_next
                   else
                     ((&0:int) <= ival sx - ival index /\
                      ival sx - ival next < ival sx - ival index) /\
                     wmpnadd_carry_invariant
                       offset pelts sy sx r x y next carry
                       r_next x_next y_next))))
     else
       wmpnadd_final_state
         offset pelts sy sx r x y current x_current y_current carry`;;

let wmpnadd_carry_loop = new_definition
  `wmpnadd_carry_loop
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
     !index:int32. !carry:int64.
     !y_current x_current current:'p.
       wmpnadd_rebased_snapshot
         data_length pelts offset minimum maximum writable zone
         y_current current y_initial
       ==>
       wmpnadd_rebased_snapshot
         data_length pelts offset minimum maximum writable zone
         x_current current x_initial
       ==>
       wmpnadd_snapshot_metadata
         data_length offset minimum maximum writable zone current initial
       ==>
       wmpnadd_carry_invariant
         offset pelts sy sx r x y index carry
         current x_current y_current
       ==>
       wmpnadd_carry_step
         data_length offset minimum maximum writable zone pelts
         sy sx r x y index carry current x_current y_current`;;

let wmpnadd_carry_phase = new_definition
  `wmpnadd_carry_phase
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (carry:int64)
     (current:'p) (x_current:'p) (y_current:'p) <=>
     wmpnadd_carry_invariant
       offset pelts sy sx r x y sy carry current x_current y_current /\
     wmpnadd_carry_loop
       data_length offset minimum maximum writable zone pelts
       sy sx r x y current x_current y_current`;;

let wmpnadd_after_initial_flag = new_definition
  `wmpnadd_after_initial_flag
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (carry:int64) (flag:bool)
     (current:'p) (x_current:'p) (y_current:'p) <=>
     if ~(flag = T) then
       wmpnadd_carry_phase
         data_length offset minimum maximum writable zone pelts
         sy sx r x y carry current x_current y_current
     else
       wmpnadd_copy_phase
         data_length offset minimum maximum writable zone pelts
         sy sx r x y sy carry current x_current y_current`;;

let wmpnadd_after_initial = new_definition
  `wmpnadd_after_initial
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (carry:int64)
     (current:'p) (x_current:'p) (y_current:'p) <=>
     !flag:bool.
       wmpnadd_zero_flag carry flag
       ==>
       wmpnadd_after_initial_flag
         data_length offset minimum maximum writable zone pelts
         sy sx r x y carry flag current x_current y_current`;;

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
     wmpnadd_valid
       data_length offset minimum maximum r (ival sx)
     ==>
     wmpnadd_valid
       data_length offset minimum maximum x (ival sx)
     ==>
     wmpnadd_valid
       data_length offset minimum maximum y (ival sy)
     ==>
     wmpnadd_disjoint offset r (ival sx) x (ival sx)
     ==>
     wmpnadd_disjoint offset r (ival sx) y (ival sy)
     ==>
     wmpnadd_same_data data_length pelts r x
     ==>
     wmpnadd_same_data data_length pelts x y
     ==>
     writable r = T
     ==>
     (&0:int) <= ival sy /\
     wmpnadd_valid
       data_length offset minimum maximum r (ival sy) /\
     wmpnadd_valid
       data_length offset minimum maximum x (ival sy) /\
     wmpnadd_valid
       data_length offset minimum maximum y (ival sy) /\
     wmpnadd_disjoint offset r (ival sy) x (ival sy) /\
     wmpnadd_disjoint offset r (ival sy) y (ival sy) /\
     wmpnadd_same_data data_length pelts r x /\
     wmpnadd_same_data data_length pelts x y /\
     writable r = T /\
     (!y_current x_current current:'p.
        wmpnadd_rebased_snapshot
          data_length pelts offset minimum maximum writable zone
          y_current current y
        ==>
        wmpnadd_rebased_snapshot
          data_length pelts offset minimum maximum writable zone
          x_current current x
        ==>
        wmpnadd_snapshot_metadata
          data_length offset minimum maximum writable zone current r
        ==>
        (!carry:int64.
           wmpnadd_initial_postcondition
             offset pelts sy r x y current x_current y_current carry
           ==>
           wmpnadd_after_initial
             data_length offset minimum maximum writable zone pelts
             sy sx r x y carry current x_current y_current))`;;

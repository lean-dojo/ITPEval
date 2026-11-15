(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_Sub_wmpn_sub_nqtvc: the verification condition for
  equal-length multiprecision subtraction with aliased pointer snapshots,
  including signed loop-index bounds, borrow propagation, single-limb
  updates, pointer validity, and memory framing. This file contains no proof.
*)

let subn_statement_output = open_out "/dev/null";;
Format.set_formatter_out_channel subn_statement_output;;

needs "Library/words.ml";;
needs "Library/isum.ml";;

let subn_radix = new_definition
  `subn_radix = (&18446744073709551616:int)`;;

let subn_u64 = new_definition
  `subn_u64 (x:int64) = (&(val x):int)`;;

let subn_int32_in_bounds = new_definition
  `subn_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let subn_radix_power = new_definition
  `subn_radix_power (n:int) =
     subn_radix pow (if n < (&0:int) then 0 else num_of_int n)`;;

let subn_value = new_definition
  `subn_value
     (pelts:'p->int->int64) (offset:'p->int) (p:'p) (n:int) =
     if n <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int n - 1)
         (\k. subn_radix pow k *
              subn_u64 (pelts p (offset p + &k)))`;;

let subn_valid = new_definition
  `subn_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (n:int) <=>
     subn_int32_in_bounds n /\
     (&0:int) <= n /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + n <= maximum p /\
     maximum p <= &(data_length p)`;;

let subn_same_data = new_definition
  `subn_same_data
     (data_length:'p->num)
     (pelts:'p->int->int64)
     (left:'p) (right:'p) <=>
     data_length left = data_length right /\
     pelts left = pelts right`;;

let subn_map_eq_sub = new_definition
  `subn_map_eq_sub
     (pelts:'p->int->int64)
     (left:'p) (right:'p) (lower:int) (upper:int) <=>
     !i:int.
       lower <= i /\ i < upper
       ==> pelts left i = pelts right i`;;

let subn_alias_safe = new_definition
  `subn_alias_safe
     (offset:'p->int) (result:'p) (operand:'p) (size:int) <=>
     offset result = offset operand \/
     offset result + size <= offset operand \/
     offset operand + size <= offset result`;;

let subn_rebased_snapshot = new_definition
  `subn_rebased_snapshot
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (fresh:'p) (shared:'p) (old:'p) <=>
     subn_same_data data_length pelts fresh shared /\
     data_length shared = data_length old /\
     offset fresh = offset old /\
     minimum fresh = minimum old /\
     maximum fresh = maximum old /\
     writable fresh = writable old /\
     zone fresh = zone old`;;

let subn_snapshot = new_definition
  `subn_snapshot
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

let subn_single_update = new_definition
  `subn_single_update
     (pelts:'p->int->int64)
     (fresh:'p) (old:'p) (index:int) (value:int64) <=>
     !j:int.
       pelts fresh j =
       if j = index then value else pelts old j`;;

let subn_frame = new_definition
  `subn_frame
     (offset:'p->int)
     (pelts:'p->int->int64)
     (fresh:'p) (old:'p) (size:int) <=>
     !j:int.
       j < offset fresh \/ offset fresh + size <= j
       ==> pelts fresh j = pelts old j`;;

let subn_access = new_definition
  `subn_access
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (index:int) <=>
     minimum p <= index /\ index < maximum p`;;

let subn_borrow_range = new_definition
  `subn_borrow_range (borrow:int64) <=>
     (&0:int) <= subn_u64 borrow /\
     subn_u64 borrow <= (&1:int)`;;

let subn_value_equation = new_definition
  `subn_value_equation
     (offset:'p->int)
     (pelts:'p->int->int64)
     (current:'p) (x:'p) (y:'p)
     (index:int) (borrow:int64) <=>
     subn_value pelts offset current index -
       subn_radix_power index * subn_u64 borrow =
       subn_value pelts offset x index -
       subn_value pelts offset y index`;;

let subn_alias_state = new_definition
  `subn_alias_state
     (offset:'p->int)
     (pelts:'p->int->int64)
     (size:int32)
     (current:'p) (x_current:'p) (y_current:'p)
     (x:'p) (y:'p) <=>
     pelts x_current = pelts current /\
     pelts current = pelts y_current /\
     (offset current = offset x_current \/
      subn_map_eq_sub
        pelts x_current x
        (offset x_current) (offset x_current + ival size)) /\
     (offset current = offset y_current \/
      subn_map_eq_sub
        pelts y_current y
        (offset y_current) (offset y_current + ival size))`;;

let subn_loop_invariant = new_definition
  `subn_loop_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (size:int32)
     (initial:'p) (x:'p) (y:'p)
     (index:int32) (borrow:int64)
     (current:'p) (x_current:'p) (y_current:'p) <=>
     (&0:int) <= ival index /\
     ival index <= ival size /\
     subn_value_equation
       offset pelts current x y (ival index) borrow /\
     subn_frame offset pelts current initial (ival index) /\
     subn_alias_state
       offset pelts size current x_current y_current x y /\
     subn_borrow_range borrow`;;

let subn_final_state = new_definition
  `subn_final_state
     (offset:'p->int)
     (pelts:'p->int->int64)
     (size:int32)
     (initial:'p) (x:'p) (y:'p)
     (current:'p) (x_current:'p) (y_current:'p)
     (borrow:int64) <=>
     subn_value_equation
       offset pelts current x y (ival size) borrow /\
     subn_borrow_range borrow /\
     subn_frame offset pelts current initial (ival size) /\
     (offset current = offset x_current \/
      subn_map_eq_sub
        pelts x_current x
        (offset x_current) (offset x_current + ival size)) /\
     (offset current = offset y_current \/
      subn_map_eq_sub
        pelts y_current y
        (offset y_current) (offset y_current + ival size))`;;

let subn_after_update = new_definition
  `subn_after_update
     (offset:'p->int)
     (pelts:'p->int->int64)
     (size:int32)
     (initial:'p) (x:'p) (y:'p)
     (index:int32) (borrow:int64)
     (updated:'p) (x_updated:'p) (y_updated:'p) <=>
     subn_int32_in_bounds (ival index + (&1:int)) /\
     (!next:int32.
        ival next = ival index + (&1:int)
        ==>
        ((&0:int) <= ival size - ival index /\
         ival size - ival next < ival size - ival index) /\
        subn_loop_invariant
          offset pelts size initial x y next borrow
          updated x_updated y_updated)`;;

let subn_subtraction_step = new_definition
  `subn_subtraction_step
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (size:int32)
     (initial:'p) (x:'p) (y:'p)
     (index:int32) (incoming:int64)
     (current:'p) (x_current:'p) (y_current:'p) <=>
     subn_access
       minimum maximum x_current (offset x_current + ival index) /\
     subn_access
       minimum maximum y_current (offset y_current + ival index) /\
     subn_access minimum maximum x (offset x + ival index) /\
     subn_access minimum maximum y (offset y + ival index) /\
     subn_borrow_range incoming /\
     (!result:int64. !outgoing:int64.
        subn_u64 result -
          subn_radix * subn_u64 outgoing =
          subn_u64
            (pelts x_current (offset x_current + ival index)) -
          subn_u64
            (pelts y_current (offset y_current + ival index)) -
          subn_u64 incoming /\
        subn_borrow_range outgoing
        ==>
        (subn_access
           minimum maximum current (offset current + ival index) /\
         writable current = T) /\
        (!y_updated x_updated updated:'p.
           subn_rebased_snapshot
             data_length offset minimum maximum writable zone pelts
             y_updated updated y_current
           ==>
           subn_rebased_snapshot
             data_length offset minimum maximum writable zone pelts
             x_updated updated x_current
           ==>
           subn_snapshot
             data_length offset minimum maximum writable zone
             updated current
           ==>
           (subn_single_update
              pelts updated current (offset updated + ival index) result /\
            pelts updated (offset updated + ival index) = result)
           ==>
           subn_after_update
             offset pelts size initial x y index outgoing
             updated x_updated y_updated))`;;

let subn_loop_step = new_definition
  `subn_loop_step
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (size:int32)
     (initial:'p) (x:'p) (y:'p)
     (index:int32) (borrow:int64)
     (current:'p) (x_current:'p) (y_current:'p) <=>
     if ival index < ival size then
       subn_subtraction_step
         data_length offset minimum maximum writable zone pelts
         size initial x y index borrow current x_current y_current
     else
       subn_final_state
         offset pelts size initial x y current x_current y_current borrow`;;

let statement =
  `!data_length:'p->num.
   !offset minimum maximum:'p->int.
   !writable:'p->bool.
   !zone:'p->'z.
   !pelts:'p->int->int64.
   !size:int32. !r x y:'p.
     (&0:int) <= ival size
     ==>
     subn_valid
       data_length offset minimum maximum r (ival size)
     ==>
     subn_valid
       data_length offset minimum maximum x (ival size)
     ==>
     subn_valid
       data_length offset minimum maximum y (ival size)
     ==>
     subn_alias_safe offset r x (ival size)
     ==>
     subn_alias_safe offset r y (ival size)
     ==>
     subn_same_data data_length pelts r x
     ==>
     subn_same_data data_length pelts x y
     ==>
     writable r = T
     ==>
     (&0:int) <= (&0:int) /\
     (&0:int) <= ival size /\
     subn_value pelts offset r (&0:int) -
       subn_radix_power (&0:int) * (&0:int) =
       subn_value pelts offset x (&0:int) -
       subn_value pelts offset y (&0:int) /\
     pelts x = pelts r /\
     pelts r = pelts y /\
     (offset r = offset x \/
      subn_map_eq_sub
        pelts x x (offset x) (offset x + ival size)) /\
     (offset r = offset y \/
      subn_map_eq_sub
        pelts y y (offset y) (offset y + ival size)) /\
     (&0:int) <= (&0:int) /\
     (&0:int) <= (&1:int) /\
     (!index:int32. !borrow:int64.
      !y_current x_current current:'p.
        subn_rebased_snapshot
          data_length offset minimum maximum writable zone pelts
          y_current current y
        ==>
        subn_rebased_snapshot
          data_length offset minimum maximum writable zone pelts
          x_current current x
        ==>
        subn_snapshot
          data_length offset minimum maximum writable zone current r
        ==>
        subn_loop_invariant
          offset pelts size r x y index borrow
          current x_current y_current
        ==>
        subn_loop_step
          data_length offset minimum maximum writable zone pelts
          size r x y index borrow current x_current y_current)`;;

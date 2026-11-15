(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_SubOld_wmpn_subqtvc: the verification condition for
  unequal-length multiprecision subtraction into a separate destination,
  including borrow propagation, copying of remaining limbs, pointer validity,
  single-limb updates, loop invariants, and memory framing. This file contains
  no proof.
*)

let mpsub_statement_output = open_out "/dev/null";;
Format.set_formatter_out_channel mpsub_statement_output;;

needs "Library/words.ml";;
needs "Library/isum.ml";;

let mpsub_radix = new_definition
  `mpsub_radix = (&18446744073709551616:int)`;;

let mpsub_u64 = new_definition
  `mpsub_u64 (x:int64) = (&(val x):int)`;;

let mpsub_int32_in_bounds = new_definition
  `mpsub_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let mpsub_radix_power = new_definition
  `mpsub_radix_power (n:int) =
     mpsub_radix pow (if n < (&0:int) then 0 else num_of_int n)`;;

let mpsub_value = new_definition
  `mpsub_value
     (pelts:'p->int->int64) (offset:'p->int) (p:'p) (n:int) =
     if n <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int n - 1)
         (\k. mpsub_radix pow k *
              mpsub_u64 (pelts p (offset p + &k)))`;;

let mpsub_valid = new_definition
  `mpsub_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (n:int) <=>
     mpsub_int32_in_bounds n /\
     (&0:int) <= n /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + n <= maximum p /\
     maximum p <= &(data_length p)`;;

let mpsub_same_snapshot = new_definition
  `mpsub_same_snapshot
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (new:'p) (old:'p) <=>
     data_length new = data_length old /\
     offset new = offset old /\
     minimum new = minimum old /\
     maximum new = maximum old /\
     writable new = writable old /\
     zone new = zone old`;;

let mpsub_single_update = new_definition
  `mpsub_single_update
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (index:int) (value:int64) <=>
     !j:int.
       pelts new j =
       if j = index then value else pelts old j`;;

let mpsub_frame = new_definition
  `mpsub_frame
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (count:int) <=>
     !j:int.
       j < offset new \/ offset new + count <= j
       ==> pelts new j = pelts old j`;;

let mpsub_access = new_definition
  `mpsub_access
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (index:int) <=>
     minimum p <= index /\ index < maximum p`;;

let mpsub_borrow_range = new_definition
  `mpsub_borrow_range (borrow:int64) <=>
     (&0:int) <= mpsub_u64 borrow /\
     mpsub_u64 borrow <= (&1:int)`;;

let mpsub_zero_flag = new_definition
  `mpsub_zero_flag (limb:int64) (flag:bool) <=>
     (mpsub_u64 limb = mpsub_u64 (word 0:int64)
      ==> flag = T) /\
     (flag = T ==> limb = (word 0:int64))`;;

let mpsub_value_equation = new_definition
  `mpsub_value_equation
     (offset:'p->int)
     (pelts:'p->int->int64)
     (current:'p) (x:'p) (y:'p)
     (size:int) (ysize:int) (borrow:int64) <=>
     mpsub_value pelts offset current size -
       mpsub_radix_power size * mpsub_u64 borrow =
       mpsub_value pelts offset x size -
       mpsub_value pelts offset y ysize`;;

let mpsub_initial_postcondition = new_definition
  `mpsub_initial_postcondition
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32)
     (r:'p) (x:'p) (y:'p)
     (current:'p) (borrow:int64) <=>
     mpsub_borrow_range borrow /\
     mpsub_value_equation
       offset pelts current x y (ival sy) (ival sy) borrow /\
     mpsub_frame offset pelts current r (ival sy)`;;

let mpsub_final_state = new_definition
  `mpsub_final_state
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (current:'p) (borrow:int64) <=>
     mpsub_value_equation
       offset pelts current x y (ival sx) (ival sy) borrow /\
     mpsub_frame offset pelts current r (ival sx) /\
     mpsub_borrow_range borrow`;;

let mpsub_borrow_invariant = new_definition
  `mpsub_borrow_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (index:int32) (borrow:int64) (current:'p) <=>
     ival sy <= ival index /\ ival index <= ival sx /\
     mpsub_value_equation
       offset pelts current x y (ival index) (ival sy) borrow /\
     mpsub_frame offset pelts current r (ival sx) /\
     mpsub_borrow_range borrow /\
     (index = sx \/ mpsub_u64 borrow = (&1:int))`;;

let mpsub_copy_invariant = new_definition
  `mpsub_copy_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (index:int32) (borrow:int64) (current:'p) <=>
     ival sy <= ival index /\ ival index <= ival sx /\
     (index = sx \/ mpsub_u64 borrow = (&0:int)) /\
     mpsub_value_equation
       offset pelts current x y (ival index) (ival sy) borrow /\
     mpsub_frame offset pelts current r (ival sx)`;;

let mpsub_copy_after_update = new_definition
  `mpsub_copy_after_update
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (index:int32) (borrow:int64) (updated:'p) <=>
     mpsub_int32_in_bounds (ival index + (&1:int)) /\
     (!next:int32.
        ival next = ival index + (&1:int)
        ==>
        ((&0:int) <= ival sx - ival index /\
         ival sx - ival next < ival sx - ival index) /\
        mpsub_copy_invariant
          offset pelts sy sx r x y next borrow updated)`;;

let mpsub_copy_step = new_definition
  `mpsub_copy_step
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (index:int32) (borrow:int64) (current:'p) <=>
     if ival index < ival sx then
       mpsub_access minimum maximum x (offset x + ival index) /\
       (mpsub_access
          minimum maximum current (offset current + ival index) /\
        writable current = T) /\
       (!updated:'p.
          mpsub_same_snapshot
            data_length offset minimum maximum writable zone
            updated current
          ==>
          (mpsub_single_update
             pelts updated current (offset updated + ival index)
             (pelts x (offset x + ival index)) /\
           pelts updated (offset updated + ival index) =
             pelts x (offset x + ival index))
          ==>
          mpsub_copy_after_update
            offset pelts sy sx r x y index borrow updated)
     else
       mpsub_final_state
         offset pelts sy sx r x y current borrow`;;

let mpsub_copy_loop = new_definition
  `mpsub_copy_loop
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (borrow:int64) (initial:'p) <=>
     !index:int32. !current:'p.
       mpsub_same_snapshot
         data_length offset minimum maximum writable zone current initial
       ==>
       mpsub_copy_invariant
         offset pelts sy sx r x y index borrow current
       ==>
       mpsub_copy_step
         data_length offset minimum maximum writable zone pelts
         sy sx r x y index borrow current`;;

let mpsub_copy_phase = new_definition
  `mpsub_copy_phase
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (index:int32) (borrow:int64) (current:'p) <=>
     mpsub_copy_invariant
       offset pelts sy sx r x y index borrow current /\
     mpsub_copy_loop
       data_length offset minimum maximum writable zone pelts
       sy sx r x y borrow current`;;

let mpsub_borrow_after_increment = new_definition
  `mpsub_borrow_after_increment
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (index:int32) (borrow:int64) (updated:'p)
     (next:int32) (old_limb:int64) <=>
     !flag:bool.
       mpsub_zero_flag old_limb flag
       ==>
       if ~(flag = T) then
         mpsub_copy_phase
           data_length offset minimum maximum writable zone pelts
           sy sx r x y next (word 0:int64) updated
       else
         ((&0:int) <= ival sx - ival index /\
          ival sx - ival next < ival sx - ival index) /\
         mpsub_borrow_invariant
           offset pelts sy sx r x y next borrow updated`;;

let mpsub_borrow_after_update = new_definition
  `mpsub_borrow_after_update
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (index:int32) (borrow:int64) (updated:'p)
     (old_limb:int64) <=>
     mpsub_int32_in_bounds (ival index + (&1:int)) /\
     (!next:int32.
        ival next = ival index + (&1:int)
        ==>
        mpsub_borrow_after_increment
          data_length offset minimum maximum writable zone pelts
          sy sx r x y index borrow updated next old_limb)`;;

let mpsub_borrow_step = new_definition
  `mpsub_borrow_step
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (index:int32) (borrow:int64) (current:'p) <=>
     if ival index < ival sx then
       mpsub_access minimum maximum x (offset x + ival index) /\
       (!result:int64.
          mpsub_u64 result =
            (mpsub_u64 (pelts x (offset x + ival index)) -
             (&1:int)) rem mpsub_radix
          ==>
          (mpsub_access
             minimum maximum current (offset current + ival index) /\
           writable current = T) /\
          (!updated:'p.
             mpsub_same_snapshot
               data_length offset minimum maximum writable zone
               updated current
             ==>
             (mpsub_single_update
                pelts updated current (offset updated + ival index) result /\
              pelts updated (offset updated + ival index) = result)
             ==>
             mpsub_borrow_after_update
               data_length offset minimum maximum writable zone pelts
               sy sx r x y index borrow updated
               (pelts x (offset x + ival index))))
     else
       mpsub_copy_phase
         data_length offset minimum maximum writable zone pelts
         sy sx r x y index borrow current`;;

let mpsub_borrow_loop = new_definition
  `mpsub_borrow_loop
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (initial:'p) <=>
     !index:int32. !borrow:int64. !current:'p.
       mpsub_same_snapshot
         data_length offset minimum maximum writable zone current initial
       ==>
       mpsub_borrow_invariant
         offset pelts sy sx r x y index borrow current
       ==>
       mpsub_borrow_step
         data_length offset minimum maximum writable zone pelts
         sy sx r x y index borrow current`;;

let mpsub_borrow_phase = new_definition
  `mpsub_borrow_phase
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (borrow:int64) (current:'p) <=>
     mpsub_borrow_invariant
       offset pelts sy sx r x y sy borrow current /\
     mpsub_borrow_loop
       data_length offset minimum maximum writable zone pelts
       sy sx r x y current`;;

let mpsub_after_initial_flag = new_definition
  `mpsub_after_initial_flag
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (borrow:int64) (flag:bool) (current:'p) <=>
     if ~(flag = T) then
       mpsub_borrow_phase
         data_length offset minimum maximum writable zone pelts
         sy sx r x y borrow current
     else
       mpsub_copy_phase
         data_length offset minimum maximum writable zone pelts
         sy sx r x y sy borrow current`;;

let mpsub_after_initial = new_definition
  `mpsub_after_initial
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (r:'p) (x:'p) (y:'p)
     (borrow:int64) (current:'p) <=>
     !flag:bool.
       mpsub_zero_flag borrow flag
       ==>
       mpsub_after_initial_flag
         data_length offset minimum maximum writable zone pelts
         sy sx r x y borrow flag current`;;

let statement =
  `!data_length:'p->num.
   !offset minimum maximum:'p->int.
   !writable:'p->bool.
   !zone:'p->'z.
   !pelts:'p->int->int64.
   !sy sx:int32. !x y r:'p.
     (&0:int) <= ival sy
     ==>
     ival sy <= ival sx
     ==>
     mpsub_valid
       data_length offset minimum maximum x (ival sx)
     ==>
     mpsub_valid
       data_length offset minimum maximum y (ival sy)
     ==>
     mpsub_valid
       data_length offset minimum maximum r (ival sx)
     ==>
     writable r = T
     ==>
     mpsub_valid
       data_length offset minimum maximum x (ival sy) /\
     mpsub_valid
       data_length offset minimum maximum y (ival sy) /\
     mpsub_valid
       data_length offset minimum maximum r (ival sy) /\
     writable r = T /\
     (!current:'p.
        mpsub_same_snapshot
          data_length offset minimum maximum writable zone current r
        ==>
        (!borrow:int64.
           mpsub_initial_postcondition
             offset pelts sy r x y current borrow
           ==>
           mpsub_after_initial
             data_length offset minimum maximum writable zone pelts
             sy sx r x y borrow current))`;;

(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/add_AddOld_wmpn_add_in_placeqtvc: the verification
  condition for in-place unequal-length multiprecision addition, including
  carry propagation, pointer validity, updates, and memory framing. This file
  contains no proof.
*)

needs "Library/words.ml";;
needs "Library/isum.ml";;

let mpaddold_radix = new_definition
  `mpaddold_radix = (&18446744073709551616:int)`;;

let mpaddold_int32_in_bounds = new_definition
  `mpaddold_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let mpaddold_radix_power = new_definition
  `mpaddold_radix_power (n:int) =
     mpaddold_radix pow (if n < (&0:int) then 0 else num_of_int n)`;;

let mpaddold_value = new_definition
  `mpaddold_value
     (pelts:'p->int->int64) (offset:'p->int) (p:'p) (n:int) =
     if n <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int n - 1)
         (\k. mpaddold_radix pow k *
              (&(val (pelts p (offset p + &k))):int))`;;

let mpaddold_valid = new_definition
  `mpaddold_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (n:int) <=>
     mpaddold_int32_in_bounds n /\
     (&0:int) <= n /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + n <= maximum p /\
     maximum p <= &(data_length p)`;;

let mpaddold_same_snapshot = new_definition
  `mpaddold_same_snapshot
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

let mpaddold_single_update = new_definition
  `mpaddold_single_update
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (index:int) (value:int64) <=>
     !j:int.
       pelts new j =
       if j = index then value else pelts old j`;;

let mpaddold_frame = new_definition
  `mpaddold_frame
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (count:int) <=>
     !j:int.
       j < offset new \/ offset new + count <= j
       ==> pelts new j = pelts old j`;;

let mpaddold_tail_equal = new_definition
  `mpaddold_tail_equal
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (start:int) (size:int) <=>
     !j:int.
       start <= j /\ j < size
       ==> pelts new (offset new + j) = pelts old (offset new + j)`;;

let mpaddold_access = new_definition
  `mpaddold_access
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (index:int) <=>
     minimum p <= index /\ index < maximum p`;;

let mpaddold_carry_range = new_definition
  `mpaddold_carry_range (carry:int64) <=>
     (&0:int) <= (&(val carry):int) /\
     (&(val carry):int) <= (&1:int)`;;

let mpaddold_value_equation = new_definition
  `mpaddold_value_equation
     (offset:'p->int)
     (pelts:'p->int->int64)
     (current:'p) (old:'p) (y:'p)
     (size:int) (ysize:int) (carry:int64) <=>
     mpaddold_value pelts offset current size +
       mpaddold_radix_power size * (&(val carry):int) =
       mpaddold_value pelts offset old size +
       mpaddold_value pelts offset y ysize`;;

let mpaddold_zero_flag = new_definition
  `mpaddold_zero_flag (limb:int64) (flag:bool) <=>
     ((&(val limb):int) = (&(val (word 0:int64)):int) ==> flag = T) /\
     (flag = T ==> limb = (word 0:int64))`;;

let mpaddold_final_state = new_definition
  `mpaddold_final_state
     (offset:'p->int)
     (pelts:'p->int->int64)
     (current:'p) (old:'p) (y:'p)
     (size:int) (ysize:int) (carry:int64) <=>
     mpaddold_value_equation
       offset pelts current old y size ysize carry /\
     mpaddold_carry_range carry /\
     mpaddold_frame offset pelts current old size`;;

let mpaddold_loop_invariant = new_definition
  `mpaddold_loop_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (old:'p) (y:'p)
     (i:int32) (carry:int64) (current:'p) <=>
     ival sy <= ival i /\ ival i <= ival sx /\
     mpaddold_value_equation
       offset pelts current old y (ival i) (ival sy) carry /\
     mpaddold_carry_range carry /\
     (i = sx \/ (&(val carry):int) = (&1:int)) /\
     mpaddold_tail_equal
       offset pelts current old (ival i) (ival sx) /\
     mpaddold_frame offset pelts current old (ival sx)`;;

let mpaddold_after_increment = new_definition
  `mpaddold_after_increment
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (old:'p) (y:'p)
     (i:int32) (carry:int64) (current:'p)
     (next:int32) (result:int64) (flag:bool) <=>
     if ~(flag = T) then
       mpaddold_final_state
         offset pelts current old y (ival sx) (ival sy) (word 0:int64)
     else
       ((&0:int) <= ival sx - ival i /\
        ival sx - ival next < ival sx - ival i) /\
       (ival sy <= ival next /\ ival next <= ival sx) /\
       mpaddold_value_equation
         offset pelts current old y (ival next) (ival sy) carry /\
       mpaddold_carry_range carry /\
       (next = sx \/ (&(val carry):int) = (&1:int)) /\
       mpaddold_tail_equal
         offset pelts current old (ival next) (ival sx) /\
       mpaddold_frame offset pelts current old (ival sx)`;;

let mpaddold_after_write = new_definition
  `mpaddold_after_write
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (old:'p) (y:'p)
     (i:int32) (carry:int64) (current:'p) (result:int64) <=>
     mpaddold_int32_in_bounds (ival i + (&1:int)) /\
     (!next:int32.
        ival next = ival i + (&1:int)
        ==>
        (!flag:bool.
           mpaddold_zero_flag result flag
           ==>
           mpaddold_after_increment
             offset pelts sy sx old y i carry current next result flag))`;;

let mpaddold_write_step = new_definition
  `mpaddold_write_step
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (old:'p) (y:'p)
     (i:int32) (carry:int64) (current:'p) <=>
     mpaddold_access
       offset minimum maximum current (offset current + ival i) /\
     (!result:int64.
        (&(val result):int) =
          ((&(val (pelts current (offset current + ival i))):int) +
           (&1:int)) rem mpaddold_radix
        ==>
        (mpaddold_access
           offset minimum maximum current (offset current + ival i) /\
         writable current = T) /\
        (!updated:'p.
           mpaddold_same_snapshot
             data_length offset minimum maximum writable zone
             updated current
           ==>
           (mpaddold_single_update
              pelts updated current (offset updated + ival i) result /\
            pelts updated (offset updated + ival i) = result)
           ==>
           mpaddold_after_write
             offset pelts sy sx old y i carry updated result))`;;

let mpaddold_loop_step = new_definition
  `mpaddold_loop_step
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (old:'p) (y:'p)
     (i:int32) (carry:int64) (current:'p) <=>
     if ival i < ival sx then
       mpaddold_write_step
         data_length offset minimum maximum writable zone pelts
         sy sx old y i carry current
     else
       mpaddold_final_state
         offset pelts current old y (ival sx) (ival sy) carry`;;

let mpaddold_carry_loop = new_definition
  `mpaddold_carry_loop
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (old:'p) (y:'p) (initial:'p) <=>
     !i:int32. !carry:int64. !current:'p.
       mpaddold_same_snapshot
         data_length offset minimum maximum writable zone current initial
       ==>
       mpaddold_loop_invariant
         offset pelts sy sx old y i carry current
       ==>
       mpaddold_loop_step
         data_length offset minimum maximum writable zone pelts
         sy sx old y i carry current`;;

let mpaddold_continue_after_initial = new_definition
  `mpaddold_continue_after_initial
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (old:'p) (y:'p) (current:'p) (carry:int64) <=>
     ((ival sy <= ival sy /\ ival sy <= ival sx) /\
      mpaddold_value_equation
        offset pelts current old y (ival sy) (ival sy) carry /\
      mpaddold_carry_range carry /\
      (sy = sx \/ (&(val carry):int) = (&1:int)) /\
      mpaddold_tail_equal
        offset pelts current old (ival sy) (ival sx) /\
      mpaddold_frame offset pelts current old (ival sx)) /\
     mpaddold_carry_loop
       data_length offset minimum maximum writable zone pelts
       sy sx old y current`;;

let mpaddold_after_initial_flag = new_definition
  `mpaddold_after_initial_flag
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (old:'p) (y:'p) (current:'p)
     (carry:int64) (flag:bool) <=>
     if ~(flag = T) then
       mpaddold_continue_after_initial
         data_length offset minimum maximum writable zone pelts
         sy sx old y current carry
     else
       mpaddold_final_state
         offset pelts current old y (ival sx) (ival sy) carry`;;

let mpaddold_after_initial = new_definition
  `mpaddold_after_initial
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (old:'p) (y:'p) (current:'p) (carry:int64) <=>
     !flag:bool.
       mpaddold_zero_flag carry flag
       ==>
       mpaddold_after_initial_flag
         data_length offset minimum maximum writable zone pelts
         sy sx old y current carry flag`;;

let statement =
  `!data_length:'p->num.
   !offset minimum maximum:'p->int.
   !writable:'p->bool.
   !zone:'p->'z.
   !pelts:'p->int->int64.
   !sy sx:int32. !x y:'p.
     (&0:int) <= ival sy
     ==>
     ival sy <= ival sx
     ==>
     mpaddold_valid
       data_length offset minimum maximum x (ival sx)
     ==>
     mpaddold_valid
       data_length offset minimum maximum y (ival sy)
     ==>
     writable x = T
     ==>
     mpaddold_valid
       data_length offset minimum maximum x (ival sy) /\
     mpaddold_valid
       data_length offset minimum maximum y (ival sy) /\
     writable x = T /\
     (!current:'p.
        mpaddold_same_snapshot
          data_length offset minimum maximum writable zone current x
        ==>
        (!carry:int64.
           (mpaddold_carry_range carry /\
            mpaddold_value_equation
              offset pelts current x y (ival sy) (ival sy) carry /\
            mpaddold_frame offset pelts current x (ival sy))
           ==>
           mpaddold_after_initial
             data_length offset minimum maximum writable zone pelts
             sy sx x y current carry))`;;

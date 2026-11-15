(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_SubOld_wmpn_sub_in_placeqtvc: the verification
  condition for in-place unequal-length multiprecision subtraction, including
  borrow propagation, pointer validity, single-limb updates, loop invariants,
  and memory framing. This file contains no proof.
*)

let mpsubold_statement_output = open_out "/dev/null";;
Format.set_formatter_out_channel mpsubold_statement_output;;

needs "Library/words.ml";;
needs "Library/isum.ml";;

let mpsubold_radix = new_definition
  `mpsubold_radix = (&18446744073709551616:int)`;;

let mpsubold_u64 = new_definition
  `mpsubold_u64 (x:int64) = (&(val x):int)`;;

let mpsubold_int32_in_bounds = new_definition
  `mpsubold_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let mpsubold_radix_power = new_definition
  `mpsubold_radix_power (n:int) =
     mpsubold_radix pow (if n < (&0:int) then 0 else num_of_int n)`;;

let mpsubold_value = new_definition
  `mpsubold_value
     (pelts:'p->int->int64) (offset:'p->int) (p:'p) (n:int) =
     if n <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int n - 1)
         (\k. mpsubold_radix pow k *
              mpsubold_u64 (pelts p (offset p + &k)))`;;

let mpsubold_valid = new_definition
  `mpsubold_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (n:int) <=>
     mpsubold_int32_in_bounds n /\
     (&0:int) <= n /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + n <= maximum p /\
     maximum p <= &(data_length p)`;;

let mpsubold_same_snapshot = new_definition
  `mpsubold_same_snapshot
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

let mpsubold_single_update = new_definition
  `mpsubold_single_update
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (index:int) (value:int64) <=>
     !j:int.
       pelts new j =
       if j = index then value else pelts old j`;;

let mpsubold_frame = new_definition
  `mpsubold_frame
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (count:int) <=>
     !j:int.
       j < offset new \/ offset new + count <= j
       ==> pelts new j = pelts old j`;;

let mpsubold_tail_equal = new_definition
  `mpsubold_tail_equal
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (start:int) (size:int) <=>
     !j:int.
       start <= j /\ j < size
       ==> pelts new (offset new + j) = pelts old (offset new + j)`;;

let mpsubold_access = new_definition
  `mpsubold_access
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (index:int) <=>
     minimum p <= index /\ index < maximum p`;;

let mpsubold_borrow_range = new_definition
  `mpsubold_borrow_range (borrow:int64) <=>
     (&0:int) <= mpsubold_u64 borrow /\
     mpsubold_u64 borrow <= (&1:int)`;;

let mpsubold_value_equation = new_definition
  `mpsubold_value_equation
     (offset:'p->int)
     (pelts:'p->int->int64)
     (current:'p) (old:'p) (y:'p)
     (size:int) (ysize:int) (borrow:int64) <=>
     mpsubold_value pelts offset current size -
       mpsubold_radix_power size * mpsubold_u64 borrow =
       mpsubold_value pelts offset old size -
       mpsubold_value pelts offset y ysize`;;

let mpsubold_zero_flag = new_definition
  `mpsubold_zero_flag (limb:int64) (flag:bool) <=>
     (mpsubold_u64 limb = mpsubold_u64 (word 0:int64)
      ==> flag = T) /\
     (flag = T ==> limb = (word 0:int64))`;;

let mpsubold_final_state = new_definition
  `mpsubold_final_state
     (offset:'p->int)
     (pelts:'p->int->int64)
     (current:'p) (old:'p) (y:'p)
     (size:int) (ysize:int) (borrow:int64) <=>
     mpsubold_value_equation
       offset pelts current old y size ysize borrow /\
     mpsubold_borrow_range borrow /\
     mpsubold_frame offset pelts current old size`;;

let mpsubold_loop_invariant = new_definition
  `mpsubold_loop_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (old:'p) (y:'p)
     (i:int32) (borrow:int64) (current:'p) <=>
     ival sy <= ival i /\ ival i <= ival sx /\
     mpsubold_value_equation
       offset pelts current old y (ival i) (ival sy) borrow /\
     mpsubold_borrow_range borrow /\
     (i = sx \/ mpsubold_u64 borrow = (&1:int)) /\
     mpsubold_tail_equal
       offset pelts current old (ival i) (ival sx) /\
     mpsubold_frame offset pelts current old (ival sx)`;;

let mpsubold_after_increment = new_definition
  `mpsubold_after_increment
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (old:'p) (y:'p)
     (i:int32) (borrow:int64) (current:'p)
     (next:int32) (flag:bool) <=>
     if ~(flag = T) then
       mpsubold_final_state
         offset pelts current old y (ival sx) (ival sy) (word 0:int64)
     else
       ((&0:int) <= ival sx - ival i /\
        ival sx - ival next < ival sx - ival i) /\
       (ival sy <= ival next /\ ival next <= ival sx) /\
       mpsubold_value_equation
         offset pelts current old y (ival next) (ival sy) borrow /\
       mpsubold_borrow_range borrow /\
       (next = sx \/ mpsubold_u64 borrow = (&1:int)) /\
       mpsubold_tail_equal
         offset pelts current old (ival next) (ival sx) /\
       mpsubold_frame offset pelts current old (ival sx)`;;

let mpsubold_after_write = new_definition
  `mpsubold_after_write
     (offset:'p->int)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (old:'p) (y:'p)
     (i:int32) (borrow:int64) (current:'p) (old_limb:int64) <=>
     mpsubold_int32_in_bounds (ival i + (&1:int)) /\
     (!next:int32.
        ival next = ival i + (&1:int)
        ==>
        (!flag:bool.
           mpsubold_zero_flag old_limb flag
           ==>
           mpsubold_after_increment
             offset pelts sy sx old y i borrow current next flag))`;;

let mpsubold_write_step = new_definition
  `mpsubold_write_step
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (old:'p) (y:'p)
     (i:int32) (borrow:int64) (current:'p) <=>
     mpsubold_access
       minimum maximum current (offset current + ival i) /\
     (!result:int64.
        mpsubold_u64 result =
          (mpsubold_u64 (pelts current (offset current + ival i)) -
           (&1:int)) rem mpsubold_radix
        ==>
        (mpsubold_access
           minimum maximum current (offset current + ival i) /\
         writable current = T) /\
        (!updated:'p.
           mpsubold_same_snapshot
             data_length offset minimum maximum writable zone
             updated current
           ==>
           (mpsubold_single_update
              pelts updated current (offset updated + ival i) result /\
            pelts updated (offset updated + ival i) = result)
           ==>
           mpsubold_after_write
             offset pelts sy sx old y i borrow updated
             (pelts current (offset current + ival i))))`;;

let mpsubold_loop_step = new_definition
  `mpsubold_loop_step
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (old:'p) (y:'p)
     (i:int32) (borrow:int64) (current:'p) <=>
     if ival i < ival sx then
       mpsubold_write_step
         data_length offset minimum maximum writable zone pelts
         sy sx old y i borrow current
     else
       mpsubold_final_state
         offset pelts current old y (ival sx) (ival sy) borrow`;;

let mpsubold_borrow_loop = new_definition
  `mpsubold_borrow_loop
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (old:'p) (y:'p) (initial:'p) <=>
     !i:int32. !borrow:int64. !current:'p.
       mpsubold_same_snapshot
         data_length offset minimum maximum writable zone current initial
       ==>
       mpsubold_loop_invariant
         offset pelts sy sx old y i borrow current
       ==>
       mpsubold_loop_step
         data_length offset minimum maximum writable zone pelts
         sy sx old y i borrow current`;;

let mpsubold_continue_after_initial = new_definition
  `mpsubold_continue_after_initial
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (old:'p) (y:'p) (current:'p) (borrow:int64) <=>
     ((ival sy <= ival sy /\ ival sy <= ival sx) /\
      mpsubold_value_equation
        offset pelts current old y (ival sy) (ival sy) borrow /\
      mpsubold_borrow_range borrow /\
      (sy = sx \/ mpsubold_u64 borrow = (&1:int)) /\
      mpsubold_tail_equal
        offset pelts current old (ival sy) (ival sx) /\
      mpsubold_frame offset pelts current old (ival sx)) /\
     mpsubold_borrow_loop
       data_length offset minimum maximum writable zone pelts
       sy sx old y current`;;

let mpsubold_after_initial_flag = new_definition
  `mpsubold_after_initial_flag
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (old:'p) (y:'p) (current:'p)
     (borrow:int64) (flag:bool) <=>
     if ~(flag = T) then
       mpsubold_continue_after_initial
         data_length offset minimum maximum writable zone pelts
         sy sx old y current borrow
     else
       mpsubold_final_state
         offset pelts current old y (ival sx) (ival sy) borrow`;;

let mpsubold_after_initial = new_definition
  `mpsubold_after_initial
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (sy:int32) (sx:int32)
     (old:'p) (y:'p) (current:'p) (borrow:int64) <=>
     !flag:bool.
       mpsubold_zero_flag borrow flag
       ==>
       mpsubold_after_initial_flag
         data_length offset minimum maximum writable zone pelts
         sy sx old y current borrow flag`;;

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
     mpsubold_valid
       data_length offset minimum maximum x (ival sx)
     ==>
     mpsubold_valid
       data_length offset minimum maximum y (ival sy)
     ==>
     writable x = T
     ==>
     (&0:int) <= ival sy /\
     mpsubold_valid
       data_length offset minimum maximum x (ival sy) /\
     mpsubold_valid
       data_length offset minimum maximum y (ival sy) /\
     writable x = T /\
     (!current:'p.
        mpsubold_same_snapshot
          data_length offset minimum maximum writable zone current x
        ==>
        (!borrow:int64.
           (mpsubold_value_equation
              offset pelts current x y (ival sy) (ival sy) borrow /\
            mpsubold_borrow_range borrow /\
            mpsubold_frame offset pelts current x (ival sy))
           ==>
           mpsubold_after_initial
             data_length offset minimum maximum writable zone pelts
             sy sx x y current borrow))`;;

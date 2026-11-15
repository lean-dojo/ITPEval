(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_SubOld_wmpn_sub_nqtvc: the verification condition
  for equal-length multiprecision subtraction into a separate destination,
  including signed loop-index bounds, borrow propagation, single-limb
  updates, pointer validity, and memory framing. This file contains no proof.
*)

let mpsubn_statement_output = open_out "/dev/null";;
Format.set_formatter_out_channel mpsubn_statement_output;;

needs "Library/words.ml";;
needs "Library/isum.ml";;

let mpsubn_radix = new_definition
  `mpsubn_radix = (&18446744073709551616:int)`;;

let mpsubn_u64 = new_definition
  `mpsubn_u64 (x:int64) = (&(val x):int)`;;

let mpsubn_int32_in_bounds = new_definition
  `mpsubn_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let mpsubn_radix_power = new_definition
  `mpsubn_radix_power (n:int) =
     mpsubn_radix pow (if n < (&0:int) then 0 else num_of_int n)`;;

let mpsubn_value = new_definition
  `mpsubn_value
     (pelts:'p->int->int64) (offset:'p->int) (p:'p) (n:int) =
     if n <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int n - 1)
         (\k. mpsubn_radix pow k *
              mpsubn_u64 (pelts p (offset p + &k)))`;;

let mpsubn_valid = new_definition
  `mpsubn_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (n:int) <=>
     mpsubn_int32_in_bounds n /\
     (&0:int) <= n /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + n <= maximum p /\
     maximum p <= &(data_length p)`;;

let mpsubn_same_snapshot = new_definition
  `mpsubn_same_snapshot
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

let mpsubn_single_update = new_definition
  `mpsubn_single_update
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (index:int) (value:int64) <=>
     !j:int.
       pelts new j =
       if j = index then value else pelts old j`;;

let mpsubn_frame = new_definition
  `mpsubn_frame
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (size:int) <=>
     !j:int.
       j < offset new \/ offset new + size <= j
       ==> pelts new j = pelts old j`;;

let mpsubn_access = new_definition
  `mpsubn_access
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (index:int) <=>
     minimum p <= index /\ index < maximum p`;;

let mpsubn_borrow_range = new_definition
  `mpsubn_borrow_range (borrow:int64) <=>
     (&0:int) <= mpsubn_u64 borrow /\
     mpsubn_u64 borrow <= (&1:int)`;;

let mpsubn_value_equation = new_definition
  `mpsubn_value_equation
     (offset:'p->int)
     (pelts:'p->int->int64)
     (current:'p) (x:'p) (y:'p)
     (index:int) (borrow:int64) <=>
     mpsubn_value pelts offset current index -
       mpsubn_radix_power index * mpsubn_u64 borrow =
       mpsubn_value pelts offset x index -
       mpsubn_value pelts offset y index`;;

let mpsubn_loop_invariant = new_definition
  `mpsubn_loop_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (size:int32)
     (initial:'p) (x:'p) (y:'p)
     (index:int32) (borrow:int64) (current:'p) <=>
     (&0:int) <= ival index /\
     ival index <= ival size /\
     mpsubn_value_equation
       offset pelts current x y (ival index) borrow /\
     mpsubn_frame offset pelts current initial (ival size) /\
     mpsubn_borrow_range borrow`;;

let mpsubn_final_state = new_definition
  `mpsubn_final_state
     (offset:'p->int)
     (pelts:'p->int->int64)
     (size:int32)
     (initial:'p) (x:'p) (y:'p)
     (current:'p) (borrow:int64) <=>
     mpsubn_borrow_range borrow /\
     mpsubn_value_equation
       offset pelts current x y (ival size) borrow /\
     mpsubn_frame offset pelts current initial (ival size)`;;

let mpsubn_after_update = new_definition
  `mpsubn_after_update
     (offset:'p->int)
     (pelts:'p->int->int64)
     (size:int32)
     (initial:'p) (x:'p) (y:'p)
     (index:int32) (borrow:int64) (updated:'p) <=>
     mpsubn_int32_in_bounds (ival index + (&1:int)) /\
     (!next:int32.
        ival next = ival index + (&1:int)
        ==>
        ((&0:int) <= ival size - ival index /\
         ival size - ival next < ival size - ival index) /\
        mpsubn_loop_invariant
          offset pelts size initial x y next borrow updated)`;;

let mpsubn_subtraction_step = new_definition
  `mpsubn_subtraction_step
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (size:int32)
     (initial:'p) (x:'p) (y:'p)
     (index:int32) (incoming:int64) (current:'p) <=>
     mpsubn_access
       minimum maximum x (offset x + ival index) /\
     mpsubn_access
       minimum maximum y (offset y + ival index) /\
     mpsubn_borrow_range incoming /\
     (!result:int64. !outgoing:int64.
        mpsubn_u64 result -
          mpsubn_radix * mpsubn_u64 outgoing =
          mpsubn_u64 (pelts x (offset x + ival index)) -
          mpsubn_u64 (pelts y (offset y + ival index)) -
          mpsubn_u64 incoming /\
        mpsubn_borrow_range outgoing
        ==>
        (mpsubn_access
           minimum maximum current (offset current + ival index) /\
         writable current = T) /\
        (!updated:'p.
           mpsubn_same_snapshot
             data_length offset minimum maximum writable zone
             updated current
           ==>
           (mpsubn_single_update
              pelts updated current (offset updated + ival index) result /\
            pelts updated (offset updated + ival index) = result)
           ==>
           mpsubn_after_update
             offset pelts size initial x y index outgoing updated))`;;

let mpsubn_loop_step = new_definition
  `mpsubn_loop_step
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (size:int32)
     (initial:'p) (x:'p) (y:'p)
     (index:int32) (borrow:int64) (current:'p) <=>
     if ival index < ival size then
       mpsubn_subtraction_step
         data_length offset minimum maximum writable zone pelts
         size initial x y index borrow current
     else
       mpsubn_final_state
         offset pelts size initial x y current borrow`;;

let statement =
  `!data_length:'p->num.
   !offset minimum maximum:'p->int.
   !writable:'p->bool.
   !zone:'p->'z.
   !pelts:'p->int->int64.
   !size:int32. !x y r:'p.
     mpsubn_valid
       data_length offset minimum maximum x (ival size)
     ==>
     mpsubn_valid
       data_length offset minimum maximum y (ival size)
     ==>
     mpsubn_valid
       data_length offset minimum maximum r (ival size)
     ==>
     writable r = T
     ==>
     (&0:int) <= (&0:int) /\
     (&0:int) <= ival size /\
     mpsubn_value pelts offset r (&0:int) -
       mpsubn_radix_power (&0:int) * (&0:int) =
       mpsubn_value pelts offset x (&0:int) -
       mpsubn_value pelts offset y (&0:int) /\
     (&0:int) <= (&0:int) /\
     (&0:int) <= (&1:int) /\
     (!index:int32. !borrow:int64. !current:'p.
        mpsubn_same_snapshot
          data_length offset minimum maximum writable zone current r
        ==>
        mpsubn_loop_invariant
          offset pelts size r x y index borrow current
        ==>
        mpsubn_loop_step
          data_length offset minimum maximum writable zone pelts
          size r x y index borrow current)`;;

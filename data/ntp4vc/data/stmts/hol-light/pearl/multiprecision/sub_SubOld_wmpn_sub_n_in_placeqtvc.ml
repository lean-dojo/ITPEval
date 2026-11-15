(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_SubOld_wmpn_sub_n_in_placeqtvc: the verification
  condition for equal-length in-place multiprecision subtraction, including
  signed loop-index bounds, borrow propagation, single-limb updates, and
  memory framing. This file contains no proof.
*)

let mpsubnip_statement_output = open_out "/dev/null";;
Format.set_formatter_out_channel mpsubnip_statement_output;;

needs "Library/words.ml";;
needs "Library/isum.ml";;

let mpsubnip_radix = new_definition
  `mpsubnip_radix = (&18446744073709551616:int)`;;

let mpsubnip_u64 = new_definition
  `mpsubnip_u64 (x:int64) = (&(val x):int)`;;

let mpsubnip_int32_in_bounds = new_definition
  `mpsubnip_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let mpsubnip_radix_power = new_definition
  `mpsubnip_radix_power (n:int) =
     mpsubnip_radix pow (if n < (&0:int) then 0 else num_of_int n)`;;

let mpsubnip_value = new_definition
  `mpsubnip_value
     (pelts:'p->int->int64) (offset:'p->int) (p:'p) (n:int) =
     if n <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int n - 1)
         (\k. mpsubnip_radix pow k *
              mpsubnip_u64 (pelts p (offset p + &k)))`;;

let mpsubnip_valid = new_definition
  `mpsubnip_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (n:int) <=>
     mpsubnip_int32_in_bounds n /\
     (&0:int) <= n /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + n <= maximum p /\
     maximum p <= &(data_length p)`;;

let mpsubnip_same_snapshot = new_definition
  `mpsubnip_same_snapshot
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

let mpsubnip_single_update = new_definition
  `mpsubnip_single_update
     (pelts:'p->int->int64)
     (fresh:'p) (old:'p) (index:int) (value:int64) <=>
     !j:int.
       pelts fresh j =
       if j = index then value else pelts old j`;;

let mpsubnip_access = new_definition
  `mpsubnip_access
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (index:int) <=>
     minimum p <= index /\ index < maximum p`;;

let mpsubnip_borrow_range = new_definition
  `mpsubnip_borrow_range (borrow:int64) <=>
     (&0:int) <= mpsubnip_u64 borrow /\
     mpsubnip_u64 borrow <= (&1:int)`;;

let mpsubnip_tail_equal = new_definition
  `mpsubnip_tail_equal
     (offset:'p->int)
     (pelts:'p->int->int64)
     (current:'p) (old:'p) (start:int) (size:int) <=>
     !j:int.
       start <= j /\ j < size
       ==> pelts current (offset current + j) =
           pelts old (offset current + j)`;;

let mpsubnip_frame = new_definition
  `mpsubnip_frame
     (offset:'p->int)
     (pelts:'p->int->int64)
     (current:'p) (old:'p) (size:int) <=>
     !j:int.
       j < offset current \/ offset current + size <= j
       ==> pelts current j = pelts old j`;;

let mpsubnip_value_equation = new_definition
  `mpsubnip_value_equation
     (offset:'p->int)
     (pelts:'p->int->int64)
     (current:'p) (old:'p) (y:'p)
     (index:int) (borrow:int64) <=>
     mpsubnip_value pelts offset current index -
       mpsubnip_radix_power index * mpsubnip_u64 borrow =
       mpsubnip_value pelts offset old index -
       mpsubnip_value pelts offset y index`;;

let mpsubnip_loop_invariant = new_definition
  `mpsubnip_loop_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (size:int32)
     (old:'p) (y:'p)
     (index:int32) (borrow:int64) (current:'p) <=>
     (&0:int) <= ival index /\
     ival index <= ival size /\
     mpsubnip_value_equation
       offset pelts current old y (ival index) borrow /\
     mpsubnip_borrow_range borrow /\
     mpsubnip_tail_equal
       offset pelts current old (ival index) (ival size) /\
     mpsubnip_frame offset pelts current old (ival size)`;;

let mpsubnip_final_state = new_definition
  `mpsubnip_final_state
     (offset:'p->int)
     (pelts:'p->int->int64)
     (size:int32)
     (old:'p) (y:'p) (current:'p) (borrow:int64) <=>
     mpsubnip_value_equation
       offset pelts current old y (ival size) borrow /\
     mpsubnip_borrow_range borrow /\
     mpsubnip_frame offset pelts current old (ival size)`;;

let mpsubnip_after_update = new_definition
  `mpsubnip_after_update
     (offset:'p->int)
     (pelts:'p->int->int64)
     (size:int32)
     (old:'p) (y:'p)
     (index:int32) (borrow:int64) (updated:'p) <=>
     mpsubnip_int32_in_bounds (ival index + (&1:int)) /\
     (!next:int32.
        ival next = ival index + (&1:int)
        ==>
        ((&0:int) <= ival size - ival index /\
         ival size - ival next < ival size - ival index) /\
        mpsubnip_loop_invariant
          offset pelts size old y next borrow updated)`;;

let mpsubnip_subtraction_step = new_definition
  `mpsubnip_subtraction_step
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (size:int32)
     (old:'p) (y:'p)
     (index:int32) (incoming:int64) (current:'p) <=>
     mpsubnip_access
       minimum maximum current (offset current + ival index) /\
     mpsubnip_access
       minimum maximum y (offset y + ival index) /\
     mpsubnip_borrow_range incoming /\
     (!result:int64. !outgoing:int64.
        mpsubnip_u64 result -
          mpsubnip_radix * mpsubnip_u64 outgoing =
          mpsubnip_u64
            (pelts current (offset current + ival index)) -
          mpsubnip_u64 (pelts y (offset y + ival index)) -
          mpsubnip_u64 incoming /\
        mpsubnip_borrow_range outgoing
        ==>
        (mpsubnip_access
           minimum maximum current (offset current + ival index) /\
         writable current = T) /\
        (!updated:'p.
           mpsubnip_same_snapshot
             data_length offset minimum maximum writable zone
             updated current
           ==>
           (mpsubnip_single_update
              pelts updated current (offset updated + ival index) result /\
            pelts updated (offset updated + ival index) = result)
           ==>
           mpsubnip_after_update
             offset pelts size old y index outgoing updated))`;;

let mpsubnip_loop_step = new_definition
  `mpsubnip_loop_step
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (size:int32)
     (old:'p) (y:'p)
     (index:int32) (borrow:int64) (current:'p) <=>
     if ival index < ival size then
       mpsubnip_subtraction_step
         data_length offset minimum maximum writable zone pelts
         size old y index borrow current
     else
       mpsubnip_final_state
         offset pelts size old y current borrow`;;

let statement =
  `!data_length:'p->num.
   !offset minimum maximum:'p->int.
   !writable:'p->bool.
   !zone:'p->'z.
   !pelts:'p->int->int64.
   !size:int32. !x y:'p.
     (&0:int) <= ival size
     ==>
     mpsubnip_valid
       data_length offset minimum maximum x (ival size)
     ==>
     mpsubnip_valid
       data_length offset minimum maximum y (ival size)
     ==>
     writable x = T
     ==>
     (&0:int) <= (&0:int) /\
     (&0:int) <= ival size /\
     mpsubnip_value pelts offset x (&0:int) -
       mpsubnip_radix_power (&0:int) * (&0:int) =
       mpsubnip_value pelts offset x (&0:int) -
       mpsubnip_value pelts offset y (&0:int) /\
     (&0:int) <= (&0:int) /\
     (&0:int) <= (&1:int) /\
     (!index:int32. !borrow:int64. !current:'p.
        mpsubnip_same_snapshot
          data_length offset minimum maximum writable zone current x
        ==>
        mpsubnip_loop_invariant
          offset pelts size x y index borrow current
        ==>
        mpsubnip_loop_step
          data_length offset minimum maximum writable zone pelts
          size x y index borrow current)`;;

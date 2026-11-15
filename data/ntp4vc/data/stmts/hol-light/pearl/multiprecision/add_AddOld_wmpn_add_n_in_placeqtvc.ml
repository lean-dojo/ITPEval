(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/add_AddOld_wmpn_add_n_in_placeqtvc: the verification
  condition for equal-length in-place multiprecision addition, including
  carry propagation, pointer validity, single-limb updates, loop invariants,
  and memory framing. This file contains no proof.
*)

needs "Library/words.ml";;
needs "Library/isum.ml";;

let mpaddn_radix = new_definition
  `mpaddn_radix = (&18446744073709551616:int)`;;

let mpaddn_int32_in_bounds = new_definition
  `mpaddn_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let mpaddn_radix_power = new_definition
  `mpaddn_radix_power (n:int) =
     mpaddn_radix pow (if n < (&0:int) then 0 else num_of_int n)`;;

let mpaddn_value = new_definition
  `mpaddn_value
     (pelts:'p->int->int64) (offset:'p->int) (p:'p) (n:int) =
     if n <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int n - 1)
         (\k. mpaddn_radix pow k *
              (&(val (pelts p (offset p + &k))):int))`;;

let mpaddn_valid = new_definition
  `mpaddn_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (n:int) <=>
     mpaddn_int32_in_bounds n /\
     (&0:int) <= n /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + n <= maximum p /\
     maximum p <= &(data_length p)`;;

let mpaddn_same_snapshot = new_definition
  `mpaddn_same_snapshot
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

let mpaddn_single_update = new_definition
  `mpaddn_single_update
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (index:int) (value:int64) <=>
     !j:int.
       pelts new j =
       if j = index then value else pelts old j`;;

let mpaddn_frame = new_definition
  `mpaddn_frame
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (size:int) <=>
     !j:int.
       j < offset new \/ offset new + size <= j
       ==> pelts new j = pelts old j`;;

let mpaddn_tail_equal = new_definition
  `mpaddn_tail_equal
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (start:int) (size:int) <=>
     !j:int.
       start <= j /\ j < size
       ==> pelts new (offset new + j) = pelts old (offset new + j)`;;

let mpaddn_access = new_definition
  `mpaddn_access
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (index:int) <=>
     minimum p <= index /\ index < maximum p`;;

let mpaddn_carry_range = new_definition
  `mpaddn_carry_range (carry:int64) <=>
     (&0:int) <= (&(val carry):int) /\
     (&(val carry):int) <= (&1:int)`;;

let mpaddn_value_equation = new_definition
  `mpaddn_value_equation
     (offset:'p->int)
     (pelts:'p->int->int64)
     (current:'p) (old:'p) (y:'p)
     (size:int) (carry:int64) <=>
     mpaddn_value pelts offset current size +
       mpaddn_radix_power size * (&(val carry):int) =
       mpaddn_value pelts offset old size +
       mpaddn_value pelts offset y size`;;

let mpaddn_loop_invariant = new_definition
  `mpaddn_loop_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (size:int32)
     (old:'p) (y:'p)
     (index:int32) (carry:int64) (current:'p) <=>
     (&0:int) <= ival index /\ ival index <= ival size /\
     mpaddn_value_equation
       offset pelts current old y (ival index) carry /\
     mpaddn_carry_range carry /\
     mpaddn_tail_equal
       offset pelts current old (ival index) (ival size) /\
     mpaddn_frame offset pelts current old (ival size)`;;

let mpaddn_add_with_carry = new_definition
  `mpaddn_add_with_carry
     (offset:'p->int)
     (pelts:'p->int->int64)
     (current:'p) (y:'p) (index:int32)
     (carry_in:int64) (result:int64) (carry_out:int64) <=>
     (&(val result):int) +
       mpaddn_radix * (&(val carry_out):int) =
       (&(val (pelts current (offset current + ival index))):int) +
       (&(val (pelts y (offset y + ival index))):int) +
       (&(val carry_in):int) /\
     mpaddn_carry_range carry_out`;;

let mpaddn_next_invariant = new_definition
  `mpaddn_next_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (size:int32)
     (old:'p) (y:'p)
     (index:int32) (next:int32)
     (carry:int64) (current:'p) <=>
     ((&0:int) <= ival size - ival index /\
      ival size - ival next < ival size - ival index) /\
     mpaddn_loop_invariant
       offset pelts size old y next carry current`;;

let mpaddn_after_write = new_definition
  `mpaddn_after_write
     (offset:'p->int)
     (pelts:'p->int->int64)
     (size:int32)
     (old:'p) (y:'p)
     (index:int32) (carry:int64) (current:'p) <=>
     mpaddn_int32_in_bounds (ival index + (&1:int)) /\
     (!next:int32.
        ival next = ival index + (&1:int)
        ==>
        mpaddn_next_invariant
          offset pelts size old y index next carry current)`;;

let mpaddn_write_step = new_definition
  `mpaddn_write_step
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (size:int32)
     (old:'p) (y:'p)
     (index:int32) (carry_in:int64) (current:'p) <=>
     mpaddn_access
       minimum maximum current (offset current + ival index) /\
     mpaddn_access
       minimum maximum y (offset y + ival index) /\
     mpaddn_carry_range carry_in /\
     (!result:int64. !carry_out:int64.
        mpaddn_add_with_carry
          offset pelts current y index carry_in result carry_out
        ==>
        (mpaddn_access
           minimum maximum current (offset current + ival index) /\
         writable current = T) /\
        (!updated:'p.
           mpaddn_same_snapshot
             data_length offset minimum maximum writable zone
             updated current
           ==>
           (mpaddn_single_update
              pelts updated current (offset updated + ival index) result /\
            pelts updated (offset updated + ival index) = result)
           ==>
           mpaddn_after_write
             offset pelts size old y index carry_out updated))`;;

let mpaddn_exit = new_definition
  `mpaddn_exit
     (offset:'p->int)
     (pelts:'p->int->int64)
     (size:int32)
     (old:'p) (y:'p)
     (carry:int64) (current:'p) <=>
     mpaddn_carry_range carry /\
     mpaddn_value_equation
       offset pelts current old y (ival size) carry /\
     mpaddn_frame offset pelts current old (ival size)`;;

let statement =
  `!data_length:'p->num.
   !offset minimum maximum:'p->int.
   !writable:'p->bool.
   !zone:'p->'z.
   !pelts:'p->int->int64.
   !x:'p. !size:int32. !y:'p.
     mpaddn_valid
       data_length offset minimum maximum x (ival size)
     ==>
     mpaddn_valid
       data_length offset minimum maximum y (ival size)
     ==>
     writable x = T
     ==>
     ((&0:int) <= (&0:int)) /\
     ((&0:int) <= ival size) /\
     (mpaddn_value pelts offset x (&0:int) +
        mpaddn_radix_power (&0:int) * (&0:int) =
      mpaddn_value pelts offset x (&0:int) +
        mpaddn_value pelts offset y (&0:int)) /\
     ((&0:int) <= (&0:int)) /\
     ((&0:int) <= (&1:int)) /\
     (!index:int32. !carry:int64. !current:'p.
        mpaddn_same_snapshot
          data_length offset minimum maximum writable zone current x
        ==>
        mpaddn_loop_invariant
          offset pelts size x y index carry current
        ==>
        if ival index < ival size then
          mpaddn_write_step
            data_length offset minimum maximum writable zone pelts
            size x y index carry current
        else
          mpaddn_exit
            offset pelts size x y carry current)`;;

(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_1_Sub_1_wmpn_sub_1_in_placeqtvc: the verification
  condition for subtracting one 64-bit limb from a positive-length
  multiprecision value in place, including borrow propagation, pointer-state
  updates, loop invariants, and memory framing. This file contains no proof.
*)

let mpsub1_statement_output = open_out "/dev/null";;
Format.set_formatter_out_channel mpsub1_statement_output;;

needs "Library/words.ml";;
needs "Library/isum.ml";;

let mpsub1_radix = new_definition
  `mpsub1_radix = (&18446744073709551616:int)`;;

let mpsub1_u64 = new_definition
  `mpsub1_u64 (x:int64) = (&(val x):int)`;;

let mpsub1_int32_in_bounds = new_definition
  `mpsub1_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let mpsub1_radix_power = new_definition
  `mpsub1_radix_power (n:int) =
     mpsub1_radix pow (if n < (&0:int) then 0 else num_of_int n)`;;

let mpsub1_value = new_definition
  `mpsub1_value
     (pelts:'p->int->int64) (offset:'p->int) (p:'p) (n:int) =
     if n <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int n - 1)
         (\k. mpsub1_radix pow k *
              mpsub1_u64 (pelts p (offset p + &k)))`;;

let mpsub1_valid = new_definition
  `mpsub1_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (n:int) <=>
     mpsub1_int32_in_bounds n /\
     (&0:int) <= n /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + n <= maximum p /\
     maximum p <= &(data_length p)`;;

let mpsub1_access = new_definition
  `mpsub1_access
     (minimum:'p->int) (maximum:'p->int) (p:'p) (index:int) <=>
     minimum p <= index /\ index < maximum p`;;

let mpsub1_snapshot_metadata = new_definition
  `mpsub1_snapshot_metadata
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

let mpsub1_single_update = new_definition
  `mpsub1_single_update
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (index:int) (value:int64) <=>
     !j:int.
       pelts new j = if j = index then value else pelts old j`;;

let mpsub1_frame = new_definition
  `mpsub1_frame
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (size:int) <=>
     !j:int.
       j < offset new \/ offset new + size <= j
       ==> pelts new j = pelts old j`;;

let mpsub1_final_state = new_definition
  `mpsub1_final_state
     (offset:'p->int)
     (pelts:'p->int->int64)
     (memory:'p) (old:'p) (size:int32)
     (subtrahend:int64) (borrow:int) <=>
     mpsub1_value pelts offset memory (ival size) -
       mpsub1_radix_power (ival size) * borrow =
       mpsub1_value pelts offset old (ival size) -
       mpsub1_u64 subtrahend /\
     ((&0:int) <= borrow /\ borrow <= (&1:int)) /\
     mpsub1_frame offset pelts memory old (ival size)`;;

let mpsub1_initial_borrow_invariant = new_definition
  `mpsub1_initial_borrow_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (memory:'p) (old:'p) (size:int32) (subtrahend:int64) <=>
     ((&1:int) <= (&1:int) /\ (&1:int) <= ival size) /\
     ((&0:int) <= mpsub1_u64 (word 1:int64) /\
      mpsub1_u64 (word 1:int64) <= (&1:int)) /\
     (mpsub1_u64 (word 1:int64) = (&1:int) \/
      (word 1:int32) = size) /\
     mpsub1_value pelts offset memory (&1:int) -
       mpsub1_radix_power (&1:int) * mpsub1_u64 (word 1:int64) =
       mpsub1_value pelts offset old (&1:int) -
       mpsub1_u64 subtrahend /\
     mpsub1_frame offset pelts memory old (&1:int)`;;

let mpsub1_loop_invariant = new_definition
  `mpsub1_loop_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (memory:'p) (old:'p) (index:int32) (borrow:int64)
     (size:int32) (subtrahend:int64) <=>
     ((&1:int) <= ival index /\ ival index <= ival size) /\
     ((&0:int) <= mpsub1_u64 borrow /\
      mpsub1_u64 borrow <= (&1:int)) /\
     (mpsub1_u64 borrow = (&1:int) \/ index = size) /\
     mpsub1_value pelts offset memory (ival index) -
       mpsub1_radix_power (ival index) * mpsub1_u64 borrow =
       mpsub1_value pelts offset old (ival index) -
       mpsub1_u64 subtrahend /\
     mpsub1_frame offset pelts memory old (ival index)`;;

let mpsub1_zero_relation = new_definition
  `mpsub1_zero_relation (limb:int64) (flag:bool) <=>
     (mpsub1_u64 limb = mpsub1_u64 (word 0:int64) ==> flag = T) /\
     (flag = T ==> limb = (word 0:int64))`;;

let mpsub1_after_zero_test = new_definition
  `mpsub1_after_zero_test
     (offset:'p->int)
     (pelts:'p->int->int64)
     (memory:'p) (old:'p) (previous_index:int32)
     (next_index:int32) (borrow:int64)
     (size:int32) (subtrahend:int64) (flag:bool) <=>
     if ~(flag = T) then
       mpsub1_final_state
         offset pelts memory old size subtrahend
         (mpsub1_u64 (word 0:int64))
     else
       ((&0:int) <= ival size - ival previous_index /\
        ival size - ival next_index <
          ival size - ival previous_index) /\
       mpsub1_loop_invariant
         offset pelts memory old next_index borrow size subtrahend`;;

let mpsub1_after_loop_write = new_definition
  `mpsub1_after_loop_write
     (offset:'p->int)
     (pelts:'p->int->int64)
     (memory:'p) (old:'p) (previous_index:int32)
     (borrow:int64) (size:int32) (subtrahend:int64)
     (old_limb:int64) <=>
     mpsub1_int32_in_bounds (ival previous_index + (&1:int)) /\
     (!next_index:int32.
        ival next_index = ival previous_index + (&1:int)
        ==>
        (!flag:bool.
           mpsub1_zero_relation old_limb flag
           ==>
           mpsub1_after_zero_test
             offset pelts memory old previous_index next_index
             borrow size subtrahend flag))`;;

let mpsub1_loop_result = new_definition
  `mpsub1_loop_result
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (memory:'p) (old:'p) (index:int32) (borrow:int64)
     (size:int32) (subtrahend:int64) <=>
     mpsub1_access
       minimum maximum memory (offset memory + ival index) /\
     (!result:int64.
        mpsub1_u64 result =
          (mpsub1_u64 (pelts memory (offset memory + ival index)) -
           (&1:int)) rem mpsub1_radix
        ==>
        (mpsub1_access
           minimum maximum memory (offset memory + ival index) /\
         writable memory = T) /\
        (!updated:'p.
           mpsub1_snapshot_metadata
             data_length offset minimum maximum writable zone
             updated memory
           ==>
           (mpsub1_single_update
              pelts updated memory (offset updated + ival index) result /\
            pelts updated (offset updated + ival index) = result)
           ==>
           mpsub1_after_loop_write
             offset pelts updated old index borrow size subtrahend
             (pelts memory (offset memory + ival index))))`;;

let mpsub1_loop_step = new_definition
  `mpsub1_loop_step
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (memory:'p) (old:'p) (index:int32) (borrow:int64)
     (size:int32) (subtrahend:int64) <=>
     if ival index < ival size then
       mpsub1_loop_result
         data_length offset minimum maximum writable zone pelts
         memory old index borrow size subtrahend
     else
       mpsub1_final_state
         offset pelts memory old size subtrahend (mpsub1_u64 borrow)`;;

let mpsub1_loop_states = new_definition
  `mpsub1_loop_states
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (initial_memory:'p) (old:'p)
     (size:int32) (subtrahend:int64) <=>
     !index:int32. !borrow:int64. !memory:'p.
       mpsub1_snapshot_metadata
         data_length offset minimum maximum writable zone
         memory initial_memory
       ==>
       mpsub1_loop_invariant
         offset pelts memory old index borrow size subtrahend
       ==>
       mpsub1_loop_step
         data_length offset minimum maximum writable zone pelts
         memory old index borrow size subtrahend`;;

let mpsub1_after_first_write = new_definition
  `mpsub1_after_first_write
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (memory:'p) (old:'p) (size:int32) (subtrahend:int64)
     (initial_limb:int64) <=>
     if mpsub1_u64 initial_limb < mpsub1_u64 subtrahend then
       mpsub1_initial_borrow_invariant
         offset pelts memory old size subtrahend /\
       mpsub1_loop_states
         data_length offset minimum maximum writable zone pelts
         memory old size subtrahend
     else
       mpsub1_final_state
         offset pelts memory old size subtrahend (&0:int)`;;

let mpsub1_first_write_continuation = new_definition
  `mpsub1_first_write_continuation
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (old:'p) (size:int32) (subtrahend:int64)
     (initial_limb:int64) (result:int64) <=>
     !memory:'p.
       mpsub1_snapshot_metadata
         data_length offset minimum maximum writable zone memory old
       ==>
       mpsub1_single_update
         pelts memory old (offset memory) result
       ==>
       mpsub1_after_first_write
         data_length offset minimum maximum writable zone pelts
         memory old size subtrahend initial_limb`;;

let mpsub1_first_result_continuation = new_definition
  `mpsub1_first_result_continuation
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (old:'p) (size:int32) (subtrahend:int64)
     (initial_limb:int64) <=>
     !result:int64.
       mpsub1_u64 result =
         (mpsub1_u64 initial_limb - mpsub1_u64 subtrahend)
         rem mpsub1_radix
       ==>
       (mpsub1_access minimum maximum old (offset old) /\
        writable old = T) /\
       mpsub1_first_write_continuation
         data_length offset minimum maximum writable zone pelts
         old size subtrahend initial_limb result`;;

let statement =
  `!data_length:'p->num.
   !offset minimum maximum:'p->int.
   !writable:'p->bool.
   !zone:'p->'z.
   !pelts:'p->int->int64.
   !x:'p. !size:int32. !subtrahend:int64.
     mpsub1_valid
       data_length offset minimum maximum x (ival size)
     ==>
     (&0:int) < ival size
     ==>
     writable x = T
     ==>
     mpsub1_access minimum maximum x (offset x) /\
     (let initial_limb = pelts x (offset x) in
      mpsub1_first_result_continuation
        data_length offset minimum maximum writable zone pelts
        x size subtrahend initial_limb)`;;

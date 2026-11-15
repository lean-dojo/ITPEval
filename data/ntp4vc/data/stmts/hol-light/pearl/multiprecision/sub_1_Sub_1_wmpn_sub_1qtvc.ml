(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_1_Sub_1_wmpn_sub_1qtvc: the verification condition
  for subtracting one 64-bit limb from a positive-length multiprecision value
  into a separate destination, including borrow propagation, the subsequent
  copy loop, pointer-state updates, loop invariants, and memory framing. This
  file contains no proof.
*)

let mpsub1o_statement_output = open_out "/dev/null";;
Format.set_formatter_out_channel mpsub1o_statement_output;;

needs "Library/words.ml";;
needs "Library/isum.ml";;

let mpsub1o_radix = new_definition
  `mpsub1o_radix = (&18446744073709551616:int)`;;

let mpsub1o_u64 = new_definition
  `mpsub1o_u64 (x:int64) = (&(val x):int)`;;

let mpsub1o_int32_in_bounds = new_definition
  `mpsub1o_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let mpsub1o_radix_power = new_definition
  `mpsub1o_radix_power (n:int) =
     mpsub1o_radix pow (if n < (&0:int) then 0 else num_of_int n)`;;

let mpsub1o_value = new_definition
  `mpsub1o_value
     (pelts:'p->int->int64) (offset:'p->int) (p:'p) (n:int) =
     if n <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int n - 1)
         (\k. mpsub1o_radix pow k *
              mpsub1o_u64 (pelts p (offset p + &k)))`;;

let mpsub1o_valid = new_definition
  `mpsub1o_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (n:int) <=>
     mpsub1o_int32_in_bounds n /\
     (&0:int) <= n /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + n <= maximum p /\
     maximum p <= &(data_length p)`;;

let mpsub1o_access = new_definition
  `mpsub1o_access
     (minimum:'p->int) (maximum:'p->int) (p:'p) (index:int) <=>
     minimum p <= index /\ index < maximum p`;;

let mpsub1o_snapshot = new_definition
  `mpsub1o_snapshot
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

let mpsub1o_single_update = new_definition
  `mpsub1o_single_update
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (index:int) (value:int64) <=>
     !j:int.
       pelts new j = if j = index then value else pelts old j`;;

let mpsub1o_frame = new_definition
  `mpsub1o_frame
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (size:int) <=>
     !j:int.
       j < offset new \/ offset new + size <= j
       ==> pelts new j = pelts old j`;;

let mpsub1o_zero_relation = new_definition
  `mpsub1o_zero_relation (limb:int64) (flag:bool) <=>
     (mpsub1o_u64 limb = mpsub1o_u64 (word 0:int64)
      ==> flag = T) /\
     (flag = T ==> limb = (word 0:int64))`;;

let mpsub1o_borrow_invariant = new_definition
  `mpsub1o_borrow_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (memory:'p) (source:'p) (old_target:'p)
     (index:int32) (borrow:int64)
     (size:int32) (subtrahend:int64) <=>
     ((&1:int) <= ival index /\ ival index <= ival size) /\
     ((&0:int) <= mpsub1o_u64 borrow /\
      mpsub1o_u64 borrow <= (&1:int)) /\
     (index = size \/ mpsub1o_u64 borrow = (&1:int)) /\
     mpsub1o_value pelts offset memory (ival index) -
       mpsub1o_radix_power (ival index) * mpsub1o_u64 borrow =
       mpsub1o_value pelts offset source (ival index) -
       mpsub1o_u64 subtrahend /\
     mpsub1o_frame offset pelts memory old_target (ival size)`;;

let mpsub1o_copy_invariant = new_definition
  `mpsub1o_copy_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (memory:'p) (source:'p) (old_target:'p)
     (index:int32) (borrow:int64)
     (size:int32) (subtrahend:int64) <=>
     (index = size \/ mpsub1o_u64 borrow = (&0:int)) /\
     ((&0:int) <= ival index /\ ival index <= ival size) /\
     mpsub1o_value pelts offset memory (ival index) -
       mpsub1o_radix_power (ival index) * mpsub1o_u64 borrow =
       mpsub1o_value pelts offset source (ival index) -
       mpsub1o_u64 subtrahend /\
     mpsub1o_frame offset pelts memory old_target (ival size)`;;

let mpsub1o_final_state = new_definition
  `mpsub1o_final_state
     (offset:'p->int)
     (pelts:'p->int->int64)
     (memory:'p) (source:'p) (old_target:'p)
     (size:int32) (subtrahend:int64) (borrow:int64) <=>
     mpsub1o_value pelts offset memory (ival size) -
       mpsub1o_radix_power (ival size) * mpsub1o_u64 borrow =
       mpsub1o_value pelts offset source (ival size) -
       mpsub1o_u64 subtrahend /\
     mpsub1o_frame offset pelts memory old_target (ival size) /\
     (&0:int) <= mpsub1o_u64 borrow /\
     mpsub1o_u64 borrow <= (&1:int)`;;

let mpsub1o_copy_after_write = new_definition
  `mpsub1o_copy_after_write
     (offset:'p->int)
     (pelts:'p->int->int64)
     (memory:'p) (source:'p) (old_target:'p)
     (previous_index:int32) (borrow:int64)
     (size:int32) (subtrahend:int64) <=>
     mpsub1o_int32_in_bounds (ival previous_index + (&1:int)) /\
     (!next_index:int32.
        ival next_index = ival previous_index + (&1:int)
        ==>
        ((&0:int) <= ival size - ival previous_index /\
         ival size - ival next_index <
           ival size - ival previous_index) /\
        mpsub1o_copy_invariant
          offset pelts memory source old_target next_index borrow
          size subtrahend)`;;

let mpsub1o_copy_step = new_definition
  `mpsub1o_copy_step
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (memory:'p) (source:'p) (old_target:'p)
     (index:int32) (borrow:int64)
     (size:int32) (subtrahend:int64) <=>
     if ival index < ival size then
       mpsub1o_access
         minimum maximum source (offset source + ival index) /\
       (mpsub1o_access
          minimum maximum memory (offset memory + ival index) /\
        writable memory = T) /\
       (!updated:'p.
          mpsub1o_snapshot
            data_length offset minimum maximum writable zone
            updated memory
          ==>
          (mpsub1o_single_update
             pelts updated memory (offset updated + ival index)
             (pelts source (offset source + ival index)) /\
           pelts updated (offset updated + ival index) =
             pelts source (offset source + ival index))
          ==>
          mpsub1o_copy_after_write
            offset pelts updated source old_target index borrow
            size subtrahend)
     else
       mpsub1o_final_state
         offset pelts memory source old_target size subtrahend borrow`;;

let mpsub1o_copy_states = new_definition
  `mpsub1o_copy_states
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (initial_memory:'p) (source:'p) (old_target:'p)
     (borrow:int64) (size:int32) (subtrahend:int64) <=>
     !index:int32. !memory:'p.
       mpsub1o_snapshot
         data_length offset minimum maximum writable zone
         memory initial_memory
       ==>
       mpsub1o_copy_invariant
         offset pelts memory source old_target index borrow
         size subtrahend
       ==>
       mpsub1o_copy_step
         data_length offset minimum maximum writable zone pelts
         memory source old_target index borrow size subtrahend`;;

let mpsub1o_after_zero_test = new_definition
  `mpsub1o_after_zero_test
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (memory:'p) (source:'p) (old_target:'p)
     (previous_index:int32) (next_index:int32) (borrow:int64)
     (size:int32) (subtrahend:int64) (flag:bool) <=>
     if ~(flag = T) then
       mpsub1o_copy_invariant
         offset pelts memory source old_target next_index
         (word 0:int64) size subtrahend /\
       mpsub1o_copy_states
         data_length offset minimum maximum writable zone pelts
         memory source old_target (word 0:int64) size subtrahend
     else
       ((&0:int) <= ival size - ival previous_index /\
        ival size - ival next_index <
          ival size - ival previous_index) /\
       mpsub1o_borrow_invariant
         offset pelts memory source old_target next_index borrow
         size subtrahend`;;

let mpsub1o_borrow_after_write = new_definition
  `mpsub1o_borrow_after_write
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (memory:'p) (source:'p) (old_target:'p)
     (index:int32) (borrow:int64)
     (size:int32) (subtrahend:int64) (old_limb:int64) <=>
     mpsub1o_int32_in_bounds (ival index + (&1:int)) /\
     (!next_index:int32.
        ival next_index = ival index + (&1:int)
        ==>
        (!flag:bool.
           mpsub1o_zero_relation old_limb flag
           ==>
           mpsub1o_after_zero_test
             data_length offset minimum maximum writable zone pelts
             memory source old_target index next_index borrow
             size subtrahend flag))`;;

let mpsub1o_borrow_result = new_definition
  `mpsub1o_borrow_result
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (memory:'p) (source:'p) (old_target:'p)
     (index:int32) (borrow:int64)
     (size:int32) (subtrahend:int64) <=>
     mpsub1o_access
       minimum maximum source (offset source + ival index) /\
     (!result:int64.
        mpsub1o_u64 result =
          (mpsub1o_u64 (pelts source (offset source + ival index)) -
           (&1:int)) rem mpsub1o_radix
        ==>
        (mpsub1o_access
           minimum maximum memory (offset memory + ival index) /\
         writable memory = T) /\
        (!updated:'p.
           mpsub1o_snapshot
             data_length offset minimum maximum writable zone
             updated memory
           ==>
           (mpsub1o_single_update
              pelts updated memory (offset updated + ival index) result /\
            pelts updated (offset updated + ival index) = result)
           ==>
           mpsub1o_borrow_after_write
             data_length offset minimum maximum writable zone pelts
             updated source old_target index borrow size subtrahend
             (pelts source (offset source + ival index))))`;;

let mpsub1o_borrow_step = new_definition
  `mpsub1o_borrow_step
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (memory:'p) (source:'p) (old_target:'p)
     (index:int32) (borrow:int64)
     (size:int32) (subtrahend:int64) <=>
     if ival index < ival size then
       mpsub1o_borrow_result
         data_length offset minimum maximum writable zone pelts
         memory source old_target index borrow size subtrahend
     else
       mpsub1o_copy_invariant
         offset pelts memory source old_target index borrow
         size subtrahend /\
       mpsub1o_copy_states
         data_length offset minimum maximum writable zone pelts
         memory source old_target borrow size subtrahend`;;

let mpsub1o_borrow_states = new_definition
  `mpsub1o_borrow_states
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (initial_memory:'p) (source:'p) (old_target:'p)
     (size:int32) (subtrahend:int64) <=>
     !index:int32. !borrow:int64. !memory:'p.
       mpsub1o_snapshot
         data_length offset minimum maximum writable zone
         memory initial_memory
       ==>
       mpsub1o_borrow_invariant
         offset pelts memory source old_target index borrow
         size subtrahend
       ==>
       mpsub1o_borrow_step
         data_length offset minimum maximum writable zone pelts
         memory source old_target index borrow size subtrahend`;;

let mpsub1o_initial_borrow_invariant = new_definition
  `mpsub1o_initial_borrow_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (memory:'p) (source:'p) (old_target:'p)
     (size:int32) (subtrahend:int64) <=>
     ((&1:int) <= (&1:int) /\ (&1:int) <= ival size) /\
     ((&0:int) <= mpsub1o_u64 (word 1:int64) /\
      mpsub1o_u64 (word 1:int64) <= (&1:int)) /\
     ((word 1:int32) = size \/
      mpsub1o_u64 (word 1:int64) = (&1:int)) /\
     mpsub1o_value pelts offset memory (&1:int) -
       mpsub1o_radix_power (&1:int) *
       mpsub1o_u64 (word 1:int64) =
       mpsub1o_value pelts offset source (&1:int) -
       mpsub1o_u64 subtrahend /\
     mpsub1o_frame offset pelts memory old_target (ival size)`;;

let mpsub1o_initial_copy_invariant = new_definition
  `mpsub1o_initial_copy_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (memory:'p) (source:'p) (old_target:'p)
     (size:int32) (subtrahend:int64) <=>
     ((&0:int) <= (&1:int) /\ (&1:int) <= ival size) /\
     mpsub1o_value pelts offset memory (&1:int) -
       mpsub1o_radix_power (&1:int) * (&0:int) =
       mpsub1o_value pelts offset source (&1:int) -
       mpsub1o_u64 subtrahend /\
     mpsub1o_frame offset pelts memory old_target (ival size)`;;

let mpsub1o_after_first_write = new_definition
  `mpsub1o_after_first_write
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (memory:'p) (source:'p) (old_target:'p)
     (size:int32) (subtrahend:int64) (initial_limb:int64) <=>
     if mpsub1o_u64 initial_limb < mpsub1o_u64 subtrahend then
       mpsub1o_initial_borrow_invariant
         offset pelts memory source old_target size subtrahend /\
       mpsub1o_borrow_states
         data_length offset minimum maximum writable zone pelts
         memory source old_target size subtrahend
     else
       mpsub1o_initial_copy_invariant
         offset pelts memory source old_target size subtrahend /\
       mpsub1o_copy_states
         data_length offset minimum maximum writable zone pelts
         memory source old_target (word 0:int64) size subtrahend`;;

let mpsub1o_first_result = new_definition
  `mpsub1o_first_result
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (source:'p) (target:'p)
     (size:int32) (subtrahend:int64) (initial_limb:int64) <=>
     !result:int64.
       mpsub1o_u64 result =
         (mpsub1o_u64 initial_limb - mpsub1o_u64 subtrahend)
         rem mpsub1o_radix
       ==>
       (mpsub1o_access minimum maximum target (offset target) /\
        writable target = T) /\
       (!memory:'p.
          mpsub1o_snapshot
            data_length offset minimum maximum writable zone
            memory target
          ==>
          mpsub1o_single_update
            pelts memory target (offset memory) result
          ==>
          mpsub1o_after_first_write
            data_length offset minimum maximum writable zone pelts
            memory source target size subtrahend initial_limb)`;;

let statement =
  `!data_length:'p->num.
   !offset minimum maximum:'p->int.
   !writable:'p->bool.
   !zone:'p->'z.
   !pelts:'p->int->int64.
   !x:'p. !size:int32. !r:'p. !subtrahend:int64.
     mpsub1o_valid
       data_length offset minimum maximum x (ival size)
     ==>
     mpsub1o_valid
       data_length offset minimum maximum r (ival size)
     ==>
     (&0:int) < ival size
     ==>
     writable r = T
     ==>
     mpsub1o_access minimum maximum x (offset x) /\
     (let initial_limb:int64 = pelts x (offset x) in
      mpsub1o_first_result
        data_length offset minimum maximum writable zone pelts
        x r size subtrahend initial_limb)`;;

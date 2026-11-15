(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_1_Sub_1_wmpn_decr_1qtvc: the verification
  condition for decrementing a positive-length multiprecision integer in
  place by one, including borrow-loop invariants, pointer updates, and memory
  framing. This file contains no proof.
*)

needs "Library/words.ml";;
needs "Library/isum.ml";;

let mpdecr1_radix = new_definition
  `mpdecr1_radix = (&18446744073709551616:int)`;;

let mpdecr1_int32_in_bounds = new_definition
  `mpdecr1_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let mpdecr1_radix_power = new_definition
  `mpdecr1_radix_power (n:int) =
     mpdecr1_radix pow (if n < (&0:int) then 0 else num_of_int n)`;;

let mpdecr1_value = new_definition
  `mpdecr1_value
     (pelts:'p->int->int64) (offset:'p->int) (p:'p) (n:int) =
     if n <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int n - 1)
         (\k. mpdecr1_radix pow k *
              (&(val (pelts p (offset p + &k))):int))`;;

let mpdecr1_valid = new_definition
  `mpdecr1_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (n:int) <=>
     mpdecr1_int32_in_bounds n /\
     (&0:int) <= n /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + n <= maximum p /\
     maximum p <= &(data_length p)`;;

let mpdecr1_same_pelts = new_definition
  `mpdecr1_same_pelts
     (pelts:'p->int->int64) (left:'p) (right:'p) <=>
     !j:int. pelts left j = pelts right j`;;

let mpdecr1_data_eq = new_definition
  `mpdecr1_data_eq
     (data_length:'p->num)
     (pelts:'p->int->int64)
     (left:'p) (right:'p) <=>
     data_length left = data_length right /\
     mpdecr1_same_pelts pelts left right`;;

let mpdecr1_single_update = new_definition
  `mpdecr1_single_update
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (index:int) (value:int64) <=>
     !j:int.
       pelts new j = if j = index then value else pelts old j`;;

let mpdecr1_shifted_pointer = new_definition
  `mpdecr1_shifted_pointer
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (shifted:'p) (base:'p) (amount:int) <=>
     offset shifted = offset base + amount /\
     data_length shifted = data_length base /\
     mpdecr1_same_pelts pelts shifted base /\
     mpdecr1_data_eq data_length pelts shifted base /\
     minimum shifted = minimum base /\
     maximum shifted = maximum base /\
     zone shifted = zone base /\
     writable shifted = writable base`;;

let mpdecr1_loop_memory_metadata = new_definition
  `mpdecr1_loop_memory_metadata
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (memory:'p) (old:'p) <=>
     data_length memory = data_length old /\
     offset memory = offset old /\
     minimum memory = minimum old /\
     maximum memory = maximum old /\
     writable memory = writable old /\
     zone memory = zone old`;;

let mpdecr1_loop_pointer = new_definition
  `mpdecr1_loop_pointer
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (pelts:'p->int->int64)
     (pointer:'p) (memory:'p) (index:int) <=>
     offset pointer = offset memory + index /\
     mpdecr1_same_pelts pelts pointer memory /\
     data_length pointer = data_length memory /\
     minimum pointer = minimum memory /\
     maximum pointer = maximum memory`;;

let mpdecr1_tail_unchanged = new_definition
  `mpdecr1_tail_unchanged
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (start:int) (size:int) <=>
     !j:int.
       start <= j /\ j < size
       ==> pelts new (offset new + j) = pelts old (offset new + j)`;;

let mpdecr1_frame = new_definition
  `mpdecr1_frame
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (size:int) <=>
     !j:int.
       j < offset new \/ offset new + size <= j
       ==> pelts new j = pelts old j`;;

let mpdecr1_initial_invariant = new_definition
  `mpdecr1_initial_invariant
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (pelts:'p->int->int64)
     (pointer:'p) (old:'p) (size:int32) <=>
     ((&0:int) <= (&0:int) /\ (&0:int) <= ival size) /\
     ~((word 0:int32) = size) /\
     offset pointer = offset old + (&0:int) /\
     mpdecr1_same_pelts pelts pointer old /\
     data_length pointer = data_length old /\
     (minimum pointer = minimum old /\ maximum pointer = maximum old) /\
     ~((&1:int) = (&0:int)) /\
     ((&0:int) <= (&1:int) /\ (&1:int) <= (&1:int)) /\
     mpdecr1_value pelts offset old (&0:int) -
       mpdecr1_radix_power (&0:int) * (&1:int) =
       mpdecr1_value pelts offset old (&0:int) - (&1:int) /\
     writable pointer = T`;;

let mpdecr1_loop_invariant = new_definition
  `mpdecr1_loop_invariant
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (pelts:'p->int->int64)
     (old:'p) (size:int32)
     (pointer:'p) (index:int32) (last:int64) (borrow:int64)
     (memory:'p) <=>
     ((&0:int) <= ival index /\ ival index <= ival size) /\
     (index = size ==> ~((&(val last):int) = (&0:int))) /\
     mpdecr1_loop_pointer
       data_length offset minimum maximum pelts
       pointer memory (ival index) /\
     (~((&(val last):int) = (&0:int)) <=>
      (&(val borrow):int) = (&0:int)) /\
     ((&0:int) <= (&(val borrow):int) /\
      (&(val borrow):int) <= (&1:int)) /\
     mpdecr1_value pelts offset memory (ival index) -
       mpdecr1_radix_power (ival index) * (&(val borrow):int) =
       mpdecr1_value pelts offset old (ival index) - (&1:int) /\
     writable pointer = T /\
     mpdecr1_tail_unchanged
       offset pelts memory old (ival index) (ival size) /\
     mpdecr1_frame offset pelts memory old (ival size)`;;

let mpdecr1_final_state = new_definition
  `mpdecr1_final_state
     (offset:'p->int)
     (pelts:'p->int->int64)
     (memory:'p) (old:'p) (size:int32) <=>
     mpdecr1_value pelts offset memory (ival size) =
       mpdecr1_value pelts offset old (ival size) - (&1:int) /\
     mpdecr1_frame offset pelts memory old (ival size)`;;

let mpdecr1_write_metadata = new_definition
  `mpdecr1_write_metadata
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (updated:'p) (post_write:'p) (before_write:'p) <=>
     mpdecr1_data_eq data_length pelts updated post_write /\
     data_length post_write = data_length before_write /\
     offset updated = offset before_write /\
     minimum updated = minimum before_write /\
     maximum updated = maximum before_write /\
     writable updated = writable before_write /\
     zone updated = zone before_write`;;

let mpdecr1_next_loop_invariant = new_definition
  `mpdecr1_next_loop_invariant
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (pelts:'p->int->int64)
     (old:'p) (size:int32) (previous_index:int32)
     (last:int64) (memory:'p) (next_index:int32)
     (borrow:int64) (pointer:'p) <=>
     ((&0:int) <= ival size - ival previous_index /\
      ival size - ival next_index <
        ival size - ival previous_index) /\
     ((&0:int) <= ival next_index /\
      ival next_index <= ival size) /\
     (next_index = size ==> ~((&(val last):int) = (&0:int))) /\
     mpdecr1_loop_pointer
       data_length offset minimum maximum pelts
       pointer memory (ival next_index) /\
     (~((&(val last):int) = (&0:int)) <=>
      (&(val borrow):int) = (&0:int)) /\
     ((&0:int) <= (&(val borrow):int) /\
      (&(val borrow):int) <= (&1:int)) /\
     mpdecr1_value pelts offset memory (ival next_index) -
       mpdecr1_radix_power (ival next_index) * (&(val borrow):int) =
       mpdecr1_value pelts offset old (ival next_index) - (&1:int) /\
     writable pointer = T /\
     mpdecr1_tail_unchanged
       offset pelts memory old (ival next_index) (ival size) /\
     mpdecr1_frame offset pelts memory old (ival size)`;;

let mpdecr1_write_continuation = new_definition
  `mpdecr1_write_continuation
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (old:'p) (size:int32)
     (pointer:'p) (memory:'p) (index:int32)
     (last:int64) (result:int64) (borrow:int64) <=>
     !updated post_write:'p.
       mpdecr1_write_metadata
         data_length offset minimum maximum writable zone pelts
         updated post_write pointer
       ==>
       mpdecr1_write_metadata
         data_length offset minimum maximum writable zone pelts
         updated post_write pointer
       ==>
       mpdecr1_loop_memory_metadata
         data_length offset minimum maximum writable zone
         post_write memory
       ==>
       mpdecr1_single_update
         pelts updated pointer (offset updated) result
       ==>
       mpdecr1_int32_in_bounds (ival index + (&1:int)) /\
       (!next_index:int32.
          ival next_index = ival index + (&1:int)
          ==>
          (minimum updated <= offset updated + (&1:int) /\
           offset updated + (&1:int) <= maximum updated) /\
          (!next_pointer:'p.
             mpdecr1_shifted_pointer
               data_length offset minimum maximum writable zone pelts
               next_pointer updated (&1:int)
             ==>
             mpdecr1_next_loop_invariant
               data_length offset minimum maximum writable pelts
               old size index last post_write next_index borrow
               next_pointer))`;;

let mpdecr1_after_zero_test = new_definition
  `mpdecr1_after_zero_test
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (old:'p) (size:int32)
     (pointer:'p) (memory:'p) (index:int32)
     (last:int64) (result:int64) (borrow:int64) <=>
     (minimum pointer <= offset pointer /\
      offset pointer < maximum pointer) /\
     writable pointer = T /\
     mpdecr1_write_continuation
       data_length offset minimum maximum writable zone pelts
       old size pointer memory index last result borrow`;;

let mpdecr1_result_continuation = new_definition
  `mpdecr1_result_continuation
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (old:'p) (size:int32)
     (pointer:'p) (memory:'p) (index:int32) <=>
     !result:int64.
       (&(val result):int) =
         ((&(val (pelts pointer (offset pointer))):int) - (&1:int))
         rem mpdecr1_radix
       ==>
       (!zero_test:bool.
          (((&(val (pelts pointer (offset pointer))):int) =
             (&(val (word 0:int64)):int)
            ==> zero_test = T) /\
           (zero_test = T
            ==> pelts pointer (offset pointer) = (word 0:int64)))
          ==>
          if zero_test = T then
            mpdecr1_after_zero_test
              data_length offset minimum maximum writable zone pelts
              old size pointer memory index
              (pelts pointer (offset pointer)) result (word 1:int64)
          else
            mpdecr1_after_zero_test
              data_length offset minimum maximum writable zone pelts
              old size pointer memory index
              (pelts pointer (offset pointer)) result (word 0:int64))`;;

let mpdecr1_zero_last_branch = new_definition
  `mpdecr1_zero_last_branch
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (old:'p) (size:int32)
     (pointer:'p) (memory:'p) (index:int32) <=>
     (minimum pointer <= offset pointer /\
      offset pointer < maximum pointer) /\
     mpdecr1_result_continuation
       data_length offset minimum maximum writable zone pelts
       old size pointer memory index`;;

let mpdecr1_loop_result_continuation = new_definition
  `mpdecr1_loop_result_continuation
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (old:'p) (size:int32)
     (pointer:'p) (memory:'p) (index:int32) (last:int64) <=>
     !zero_test:bool.
       (((&(val last):int) = (&(val (word 0:int64)):int)
          ==> zero_test = T) /\
        (zero_test = T ==> last = (word 0:int64)))
       ==>
       if zero_test = T then
         mpdecr1_zero_last_branch
           data_length offset minimum maximum writable zone pelts
           old size pointer memory index
       else
         mpdecr1_final_state offset pelts memory old size`;;

let mpdecr1_loop_states = new_definition
  `mpdecr1_loop_states
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (old:'p) (size:int32) <=>
     !pointer:'p. !index:int32. !last:int64. !borrow:int64. !memory:'p.
       mpdecr1_loop_memory_metadata
         data_length offset minimum maximum writable zone memory old
       ==>
       mpdecr1_loop_invariant
         data_length offset minimum maximum writable pelts
         old size pointer index last borrow memory
       ==>
       mpdecr1_loop_result_continuation
         data_length offset minimum maximum writable zone pelts
         old size pointer memory index last`;;

let mpdecr1_initial_continuation = new_definition
  `mpdecr1_initial_continuation
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (old:'p) (size:int32) <=>
     !pointer:'p.
       mpdecr1_shifted_pointer
         data_length offset minimum maximum writable zone pelts
         pointer old (&0:int)
       ==>
       mpdecr1_initial_invariant
         data_length offset minimum maximum writable pelts
         pointer old size /\
       mpdecr1_loop_states
         data_length offset minimum maximum writable zone pelts old size`;;

let statement =
  `!data_length:'p->num.
   !offset minimum maximum:'p->int.
   !writable:'p->bool.
   !zone:'p->'z.
   !pelts:'p->int->int64.
   !x:'p. !size:int32.
     mpdecr1_valid
       data_length offset minimum maximum x (ival size)
     ==>
     (&0:int) < ival size
     ==>
     (&0:int) <=
       mpdecr1_value pelts offset x (ival size) - (&1:int)
     ==>
     writable x = T
     ==>
     minimum x <= offset x + (&0:int) /\
     offset x + (&0:int) <= maximum x /\
     mpdecr1_initial_continuation
       data_length offset minimum maximum writable zone pelts x size`;;

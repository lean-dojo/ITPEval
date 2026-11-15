(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/add_1_Add_1_wmpn_incr_1qtvc: the verification
  condition for incrementing a positive-length multiprecision integer in
  place by one, including carry-loop invariants, pointer updates, and memory
  framing. This file contains no proof.
*)

needs "Library/words.ml";;
needs "Library/isum.ml";;

let mpincr1_radix = new_definition
  `mpincr1_radix = (&18446744073709551616:int)`;;

let mpincr1_int32_in_bounds = new_definition
  `mpincr1_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let mpincr1_radix_power = new_definition
  `mpincr1_radix_power (n:int) =
     mpincr1_radix pow (if n < (&0:int) then 0 else num_of_int n)`;;

let mpincr1_value = new_definition
  `mpincr1_value
     (pelts:'p->int->int64) (offset:'p->int) (p:'p) (n:int) =
     if n <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int n - 1)
         (\k. mpincr1_radix pow k *
              (&(val (pelts p (offset p + &k))):int))`;;

let mpincr1_valid = new_definition
  `mpincr1_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (n:int) <=>
     mpincr1_int32_in_bounds n /\
     (&0:int) <= n /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + n <= maximum p /\
     maximum p <= &(data_length p)`;;

let mpincr1_same_pelts = new_definition
  `mpincr1_same_pelts
     (pelts:'p->int->int64) (left:'p) (right:'p) <=>
     !j:int. pelts left j = pelts right j`;;

let mpincr1_data_eq = new_definition
  `mpincr1_data_eq
     (data_length:'p->num)
     (pelts:'p->int->int64)
     (left:'p) (right:'p) <=>
     data_length left = data_length right /\
     mpincr1_same_pelts pelts left right`;;

let mpincr1_single_update = new_definition
  `mpincr1_single_update
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (index:int) (value:int64) <=>
     !j:int.
       pelts new j = if j = index then value else pelts old j`;;

let mpincr1_shifted_pointer = new_definition
  `mpincr1_shifted_pointer
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
     mpincr1_same_pelts pelts shifted base /\
     mpincr1_data_eq data_length pelts shifted base /\
     minimum shifted = minimum base /\
     maximum shifted = maximum base /\
     zone shifted = zone base /\
     writable shifted = writable base`;;

let mpincr1_loop_memory_metadata = new_definition
  `mpincr1_loop_memory_metadata
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

let mpincr1_loop_pointer = new_definition
  `mpincr1_loop_pointer
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (pelts:'p->int->int64)
     (pointer:'p) (memory:'p) (index:int) <=>
     offset pointer = offset memory + index /\
     mpincr1_same_pelts pelts pointer memory /\
     data_length pointer = data_length memory /\
     minimum pointer = minimum memory /\
     maximum pointer = maximum memory`;;

let mpincr1_tail_unchanged = new_definition
  `mpincr1_tail_unchanged
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (start:int) (size:int) <=>
     !j:int.
       start <= j /\ j < size
       ==> pelts new (offset new + j) = pelts old (offset new + j)`;;

let mpincr1_frame = new_definition
  `mpincr1_frame
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (size:int) <=>
     !j:int.
       j < offset new \/ offset new + size <= j
       ==> pelts new j = pelts old j`;;

let mpincr1_initial_invariant = new_definition
  `mpincr1_initial_invariant
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
     mpincr1_same_pelts pelts pointer old /\
     data_length pointer = data_length old /\
     (minimum pointer = minimum old /\ maximum pointer = maximum old) /\
     ~((&1:int) = (&0:int)) /\
     ((&0:int) <= (&1:int) /\ (&1:int) <= (&1:int)) /\
     writable pointer = T /\
     mpincr1_value pelts offset old (&0:int) +
       mpincr1_radix_power (&0:int) * (&1:int) =
       mpincr1_value pelts offset old (&0:int) + (&1:int)`;;

let mpincr1_loop_invariant = new_definition
  `mpincr1_loop_invariant
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (pelts:'p->int->int64)
     (old:'p) (size:int32)
     (pointer:'p) (index:int32) (carry:int64) (result:int64)
     (memory:'p) <=>
     ((&0:int) <= ival index /\ ival index <= ival size) /\
     (index = size ==> ~((&(val result):int) = (&0:int))) /\
     mpincr1_loop_pointer
       data_length offset minimum maximum pelts
       pointer memory (ival index) /\
     (~((&(val result):int) = (&0:int)) <=>
      (&(val carry):int) = (&0:int)) /\
     ((&0:int) <= (&(val carry):int) /\
      (&(val carry):int) <= (&1:int)) /\
     writable pointer = T /\
     mpincr1_value pelts offset memory (ival index) +
       mpincr1_radix_power (ival index) * (&(val carry):int) =
       mpincr1_value pelts offset old (ival index) + (&1:int) /\
     mpincr1_tail_unchanged
       offset pelts memory old (ival index) (ival size) /\
     mpincr1_frame offset pelts memory old (ival size)`;;

let mpincr1_final_state = new_definition
  `mpincr1_final_state
     (offset:'p->int)
     (pelts:'p->int->int64)
     (memory:'p) (old:'p) (size:int32) <=>
     mpincr1_value pelts offset memory (ival size) =
       mpincr1_value pelts offset old (ival size) + (&1:int) /\
     mpincr1_frame offset pelts memory old (ival size)`;;

let mpincr1_write_metadata = new_definition
  `mpincr1_write_metadata
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (updated:'p) (post_write:'p) (before_write:'p) <=>
     mpincr1_data_eq data_length pelts updated post_write /\
     data_length post_write = data_length before_write /\
     offset updated = offset before_write /\
     minimum updated = minimum before_write /\
     maximum updated = maximum before_write /\
     writable updated = writable before_write /\
     zone updated = zone before_write`;;

let mpincr1_next_loop_invariant = new_definition
  `mpincr1_next_loop_invariant
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (pelts:'p->int->int64)
     (old:'p) (size:int32) (previous_index:int32)
     (result:int64) (memory:'p) (next_index:int32)
     (carry:int64) (pointer:'p) <=>
     ((&0:int) <= ival size - ival previous_index /\
      ival size - ival next_index <
        ival size - ival previous_index) /\
     ((&0:int) <= ival next_index /\
      ival next_index <= ival size) /\
     (next_index = size ==> ~((&(val result):int) = (&0:int))) /\
     mpincr1_loop_pointer
       data_length offset minimum maximum pelts
       pointer memory (ival next_index) /\
     (~((&(val result):int) = (&0:int)) <=>
      (&(val carry):int) = (&0:int)) /\
     ((&0:int) <= (&(val carry):int) /\
      (&(val carry):int) <= (&1:int)) /\
     writable pointer = T /\
     mpincr1_value pelts offset memory (ival next_index) +
       mpincr1_radix_power (ival next_index) * (&(val carry):int) =
       mpincr1_value pelts offset old (ival next_index) + (&1:int) /\
     mpincr1_tail_unchanged
       offset pelts memory old (ival next_index) (ival size) /\
     mpincr1_frame offset pelts memory old (ival size)`;;

let mpincr1_write_continuation = new_definition
  `mpincr1_write_continuation
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (old:'p) (size:int32)
     (pointer:'p) (memory:'p) (index:int32)
     (result:int64) (carry:int64) <=>
     !updated post_write:'p.
       mpincr1_write_metadata
         data_length offset minimum maximum writable zone pelts
         updated post_write pointer
       ==>
       mpincr1_write_metadata
         data_length offset minimum maximum writable zone pelts
         updated post_write pointer
       ==>
       mpincr1_loop_memory_metadata
         data_length offset minimum maximum writable zone
         post_write memory
       ==>
       mpincr1_single_update
         pelts updated pointer (offset updated) result
       ==>
       mpincr1_int32_in_bounds (ival index + (&1:int)) /\
       (!next_index:int32.
          ival next_index = ival index + (&1:int)
          ==>
          (minimum updated <= offset updated + (&1:int) /\
           offset updated + (&1:int) <= maximum updated) /\
          (!next_pointer:'p.
             mpincr1_shifted_pointer
               data_length offset minimum maximum writable zone pelts
               next_pointer updated (&1:int)
             ==>
             mpincr1_next_loop_invariant
               data_length offset minimum maximum writable pelts
               old size index result post_write next_index carry
               next_pointer))`;;

let mpincr1_after_zero_test = new_definition
  `mpincr1_after_zero_test
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (old:'p) (size:int32)
     (pointer:'p) (memory:'p) (index:int32)
     (result:int64) (carry:int64) <=>
     (minimum pointer <= offset pointer /\
      offset pointer < maximum pointer) /\
     writable pointer = T /\
     mpincr1_write_continuation
       data_length offset minimum maximum writable zone pelts
       old size pointer memory index result carry`;;

let mpincr1_result_continuation = new_definition
  `mpincr1_result_continuation
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
         ((&(val (pelts pointer (offset pointer))):int) + (&1:int))
         rem mpincr1_radix
       ==>
       (!zero_test:bool.
          (((&(val result):int) =
             (&(val (word 0:int64)):int)
            ==> zero_test = T) /\
           (zero_test = T ==> result = (word 0:int64)))
          ==>
          if zero_test = T then
            mpincr1_after_zero_test
              data_length offset minimum maximum writable zone pelts
              old size pointer memory index result (word 1:int64)
          else
            mpincr1_after_zero_test
              data_length offset minimum maximum writable zone pelts
              old size pointer memory index result (word 0:int64))`;;

let mpincr1_zero_result_branch = new_definition
  `mpincr1_zero_result_branch
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
     mpincr1_result_continuation
       data_length offset minimum maximum writable zone pelts
       old size pointer memory index`;;

let mpincr1_loop_result_continuation = new_definition
  `mpincr1_loop_result_continuation
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (old:'p) (size:int32)
     (pointer:'p) (memory:'p) (index:int32) (result:int64) <=>
     !zero_test:bool.
       (((&(val result):int) = (&(val (word 0:int64)):int)
          ==> zero_test = T) /\
        (zero_test = T ==> result = (word 0:int64)))
       ==>
       if zero_test = T then
         mpincr1_zero_result_branch
           data_length offset minimum maximum writable zone pelts
           old size pointer memory index
       else
         mpincr1_final_state offset pelts memory old size`;;

let mpincr1_loop_states = new_definition
  `mpincr1_loop_states
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (old:'p) (size:int32) <=>
     !pointer:'p. !index:int32. !carry:int64. !result:int64. !memory:'p.
       mpincr1_loop_memory_metadata
         data_length offset minimum maximum writable zone memory old
       ==>
       mpincr1_loop_invariant
         data_length offset minimum maximum writable pelts
         old size pointer index carry result memory
       ==>
       mpincr1_loop_result_continuation
         data_length offset minimum maximum writable zone pelts
         old size pointer memory index result`;;

let mpincr1_initial_continuation = new_definition
  `mpincr1_initial_continuation
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (old:'p) (size:int32) <=>
     !pointer:'p.
       mpincr1_shifted_pointer
         data_length offset minimum maximum writable zone pelts
         pointer old (&0:int)
       ==>
       mpincr1_initial_invariant
         data_length offset minimum maximum writable pelts
         pointer old size /\
       mpincr1_loop_states
         data_length offset minimum maximum writable zone pelts old size`;;

let statement =
  `!data_length:'p->num.
   !offset minimum maximum:'p->int.
   !writable:'p->bool.
   !zone:'p->'z.
   !pelts:'p->int->int64.
   !x:'p. !size:int32.
     mpincr1_valid
       data_length offset minimum maximum x (ival size)
     ==>
     (&0:int) < ival size
     ==>
     mpincr1_value pelts offset x (ival size) + (&1:int) <
       mpincr1_radix_power (ival size)
     ==>
     writable x = T
     ==>
     minimum x <= offset x + (&0:int) /\
     offset x + (&0:int) <= maximum x /\
     mpincr1_initial_continuation
       data_length offset minimum maximum writable zone pelts x size`;;

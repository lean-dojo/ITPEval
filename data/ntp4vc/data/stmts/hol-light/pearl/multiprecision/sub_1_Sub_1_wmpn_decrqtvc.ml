(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_1_Sub_1_wmpn_decrqtvc: the verification condition
  for subtracting one 64-bit limb from a nonempty multiprecision value in
  place, including borrow-loop invariants, pointer updates, and memory
  framing. This file contains no proof.
*)

needs "Library/words.ml";;
needs "Library/isum.ml";;

let mpdecr_radix = new_definition
  `mpdecr_radix = (&18446744073709551616:int)`;;

let mpdecr_int32_in_bounds = new_definition
  `mpdecr_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let mpdecr_radix_power = new_definition
  `mpdecr_radix_power (n:int) =
     mpdecr_radix pow (if n < (&0:int) then 0 else num_of_int n)`;;

let mpdecr_value = new_definition
  `mpdecr_value
     (pelts:'p->int->int64) (offset:'p->int) (p:'p) (n:int) =
     if n <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int n - 1)
         (\k. mpdecr_radix pow k *
              (&(val (pelts p (offset p + &k))):int))`;;

let mpdecr_valid = new_definition
  `mpdecr_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (n:int) <=>
     mpdecr_int32_in_bounds n /\
     (&0:int) <= n /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + n <= maximum p /\
     maximum p <= &(data_length p)`;;

let mpdecr_same_pelts = new_definition
  `mpdecr_same_pelts
     (pelts:'p->int->int64) (left:'p) (right:'p) <=>
     !j:int. pelts left j = pelts right j`;;

let mpdecr_data_eq = new_definition
  `mpdecr_data_eq
     (data_length:'p->num)
     (pelts:'p->int->int64)
     (left:'p) (right:'p) <=>
     data_length left = data_length right /\
     mpdecr_same_pelts pelts left right`;;

let mpdecr_single_update = new_definition
  `mpdecr_single_update
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (index:int) (value:int64) <=>
     !j:int.
       pelts new j = if j = index then value else pelts old j`;;

let mpdecr_shifted_pointer = new_definition
  `mpdecr_shifted_pointer
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
     mpdecr_same_pelts pelts shifted base /\
     mpdecr_data_eq data_length pelts shifted base /\
     minimum shifted = minimum base /\
     maximum shifted = maximum base /\
     zone shifted = zone base /\
     writable shifted = writable base`;;

let mpdecr_snapshot_metadata = new_definition
  `mpdecr_snapshot_metadata
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

let mpdecr_write_metadata = new_definition
  `mpdecr_write_metadata
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (updated:'p) (post_write:'p) (before_write:'p) <=>
     mpdecr_data_eq data_length pelts updated post_write /\
     data_length post_write = data_length before_write /\
     offset updated = offset before_write /\
     minimum updated = minimum before_write /\
     maximum updated = maximum before_write /\
     writable updated = writable before_write /\
     zone updated = zone before_write`;;

let mpdecr_loop_pointer = new_definition
  `mpdecr_loop_pointer
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (pelts:'p->int->int64)
     (pointer:'p) (memory:'p) (index:int) <=>
     offset pointer = offset memory + index /\
     mpdecr_same_pelts pelts pointer memory /\
     data_length pointer = data_length memory /\
     minimum pointer = minimum memory /\
     maximum pointer = maximum memory`;;

let mpdecr_tail_unchanged = new_definition
  `mpdecr_tail_unchanged
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (start:int) (size:int) <=>
     !j:int.
       start <= j /\ j < size
       ==> pelts new (offset new + j) = pelts old (offset new + j)`;;

let mpdecr_frame = new_definition
  `mpdecr_frame
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (size:int) <=>
     !j:int.
       j < offset new \/ offset new + size <= j
       ==> pelts new j = pelts old j`;;

let mpdecr_final_state = new_definition
  `mpdecr_final_state
     (offset:'p->int)
     (pelts:'p->int->int64)
     (memory:'p) (old:'p) (size:int32) (addend:int64) <=>
     mpdecr_value pelts offset memory (ival size) =
       mpdecr_value pelts offset old (ival size) -
       (&(val addend):int) /\
     mpdecr_frame offset pelts memory old (ival size)`;;

let mpdecr_initial_loop_invariant = new_definition
  `mpdecr_initial_loop_invariant
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (pelts:'p->int->int64)
     (pointer:'p) (memory:'p) (old:'p)
     (size:int32) (addend:int64) <=>
     ((&1:int) <= (&1:int) /\ (&1:int) <= ival size) /\
     mpdecr_loop_pointer
       data_length offset minimum maximum pelts
       pointer memory (&1:int) /\
     ((word 1:int32) = size
      ==> (&(val (word 1:int64)):int) = (&0:int)) /\
     ((&0:int) <= (&(val (word 1:int64)):int) /\
      (&(val (word 1:int64)):int) <= (&1:int)) /\
     writable pointer = T /\
     mpdecr_value pelts offset memory (&1:int) -
       mpdecr_radix_power (&1:int) *
       (&(val (word 1:int64)):int) =
       mpdecr_value pelts offset old (&1:int) -
       (&(val addend):int) /\
     mpdecr_tail_unchanged
       offset pelts memory old (&1:int) (ival size) /\
     mpdecr_frame offset pelts memory old (ival size)`;;

let mpdecr_loop_invariant = new_definition
  `mpdecr_loop_invariant
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (pelts:'p->int->int64)
     (pointer:'p) (index:int32) (carry:int64)
     (memory:'p) (old:'p) (size:int32) (addend:int64) <=>
     ((&1:int) <= ival index /\ ival index <= ival size) /\
     mpdecr_loop_pointer
       data_length offset minimum maximum pelts
       pointer memory (ival index) /\
     (index = size ==> (&(val carry):int) = (&0:int)) /\
     ((&0:int) <= (&(val carry):int) /\
      (&(val carry):int) <= (&1:int)) /\
     writable pointer = T /\
     mpdecr_value pelts offset memory (ival index) -
       mpdecr_radix_power (ival index) * (&(val carry):int) =
       mpdecr_value pelts offset old (ival index) -
       (&(val addend):int) /\
     mpdecr_tail_unchanged
       offset pelts memory old (ival index) (ival size) /\
     mpdecr_frame offset pelts memory old (ival size)`;;

let mpdecr_next_loop_invariant = new_definition
  `mpdecr_next_loop_invariant
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (pelts:'p->int->int64)
     (pointer:'p) (previous_index:int32) (next_index:int32)
     (carry:int64) (memory:'p) (old:'p)
     (size:int32) (addend:int64) <=>
     ((&0:int) <= ival size - ival previous_index /\
      ival size - ival next_index <
        ival size - ival previous_index) /\
     mpdecr_loop_invariant
       data_length offset minimum maximum writable pelts
       pointer next_index carry memory old size addend`;;

let mpdecr_after_index_increment = new_definition
  `mpdecr_after_index_increment
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (updated:'p) (post_write:'p) (old:'p)
     (index:int32) (size:int32) (carry:int64)
     (addend:int64) (old_limb:int64) <=>
     mpdecr_int32_in_bounds (ival index + (&1:int)) /\
     (!next_index:int32.
        ival next_index = ival index + (&1:int)
        ==>
        (minimum updated <= offset updated + (&1:int) /\
         offset updated + (&1:int) <= maximum updated) /\
        (!pointer:'p.
           mpdecr_shifted_pointer
             data_length offset minimum maximum writable zone pelts
             pointer updated (&1:int)
           ==>
           (!zero_test:bool.
              (((&(val old_limb):int) =
                 (&(val (word 0:int64)):int)
                ==> zero_test = T) /\
               (zero_test = T ==> old_limb = (word 0:int64)))
              ==>
              if ~(zero_test = T) then
                mpdecr_final_state
                  offset pelts post_write old size addend
              else
                mpdecr_next_loop_invariant
                  data_length offset minimum maximum writable pelts
                  pointer index next_index carry post_write old
                  size addend)))`;;

let mpdecr_second_write_continuation = new_definition
  `mpdecr_second_write_continuation
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (pointer:'p) (memory:'p) (old:'p)
     (index:int32) (size:int32) (carry:int64)
     (addend:int64) (result:int64) <=>
     !updated post_write:'p.
       mpdecr_write_metadata
         data_length offset minimum maximum writable zone pelts
         updated post_write pointer
       ==>
       mpdecr_write_metadata
         data_length offset minimum maximum writable zone pelts
         updated post_write pointer
       ==>
       mpdecr_snapshot_metadata
         data_length offset minimum maximum writable zone
         post_write memory
       ==>
       mpdecr_single_update
         pelts updated pointer (offset updated) result
       ==>
       mpdecr_after_index_increment
         data_length offset minimum maximum writable zone pelts
         updated post_write old index size carry addend
         (pelts pointer (offset pointer))`;;

let mpdecr_second_result_continuation = new_definition
  `mpdecr_second_result_continuation
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (pointer:'p) (memory:'p) (old:'p)
     (index:int32) (size:int32) (carry:int64)
     (addend:int64) <=>
     (minimum pointer <= offset pointer /\
      offset pointer < maximum pointer) /\
     (!result:int64.
        (&(val result):int) =
          ((&(val (pelts pointer (offset pointer))):int) - (&1:int))
          rem mpdecr_radix
        ==>
        ((minimum pointer <= offset pointer /\
          offset pointer < maximum pointer) /\
         writable pointer = T) /\
        mpdecr_second_write_continuation
          data_length offset minimum maximum writable zone pelts
          pointer memory old index size carry addend result)`;;

let mpdecr_loop_continuation = new_definition
  `mpdecr_loop_continuation
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (pointer:'p) (memory:'p) (old:'p)
     (index:int32) (size:int32) (carry:int64)
     (addend:int64) <=>
     !zero_test:bool.
       (((&(val carry):int) = (&(val (word 0:int64)):int)
          ==> zero_test = T) /\
        (zero_test = T ==> carry = (word 0:int64)))
       ==>
       if ~(zero_test = T) then
         mpdecr_second_result_continuation
           data_length offset minimum maximum writable zone pelts
           pointer memory old index size carry addend
       else
         mpdecr_final_state offset pelts memory old size addend`;;

let mpdecr_loop_states = new_definition
  `mpdecr_loop_states
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (initial_memory:'p) (old:'p)
     (size:int32) (addend:int64) <=>
     !index:int32. !pointer:'p. !carry:int64. !memory:'p.
       mpdecr_snapshot_metadata
         data_length offset minimum maximum writable zone
         memory initial_memory
       ==>
       mpdecr_loop_invariant
         data_length offset minimum maximum writable pelts
         pointer index carry memory old size addend
       ==>
       mpdecr_loop_continuation
         data_length offset minimum maximum writable zone pelts
         pointer memory old index size carry addend`;;

let mpdecr_borrow_branch = new_definition
  `mpdecr_borrow_branch
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (pointer:'p) (memory:'p) (old:'p)
     (size:int32) (addend:int64) <=>
     mpdecr_initial_loop_invariant
       data_length offset minimum maximum writable pelts
       pointer memory old size addend /\
     mpdecr_loop_states
       data_length offset minimum maximum writable zone pelts
       memory old size addend`;;

let mpdecr_first_write_continuation = new_definition
  `mpdecr_first_write_continuation
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (shifted:'p) (old:'p) (size:int32) (addend:int64)
     (initial_limb:int64) (result:int64) <=>
     !pointer memory:'p.
       mpdecr_write_metadata
         data_length offset minimum maximum writable zone pelts
         pointer memory shifted
       ==>
       mpdecr_snapshot_metadata
         data_length offset minimum maximum writable zone memory old
       ==>
       mpdecr_single_update
         pelts memory old (offset memory) result
       ==>
       if (&(val initial_limb):int) < (&(val result):int) then
         mpdecr_borrow_branch
           data_length offset minimum maximum writable zone pelts
           pointer memory old size addend
       else
         mpdecr_final_state offset pelts memory old size addend`;;

let mpdecr_first_result_continuation = new_definition
  `mpdecr_first_result_continuation
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (shifted:'p) (old:'p) (size:int32) (addend:int64)
     (initial_limb:int64) <=>
     !result:int64.
       (&(val result):int) =
         ((&(val initial_limb):int) - (&(val addend):int))
         rem mpdecr_radix
       ==>
       ((minimum old <= offset old /\ offset old < maximum old) /\
        writable old = T) /\
       mpdecr_first_write_continuation
         data_length offset minimum maximum writable zone pelts
         shifted old size addend initial_limb result`;;

let mpdecr_shift_continuation = new_definition
  `mpdecr_shift_continuation
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (old:'p) (size:int32) (addend:int64)
     (initial_limb:int64) <=>
     !shifted:'p.
       mpdecr_shifted_pointer
         data_length offset minimum maximum writable zone pelts
         shifted old (&1:int)
       ==>
       mpdecr_first_result_continuation
         data_length offset minimum maximum writable zone pelts
         shifted old size addend initial_limb`;;

let statement =
  `!data_length:'p->num.
   !offset minimum maximum:'p->int.
   !writable:'p->bool.
   !zone:'p->'z.
   !pelts:'p->int->int64.
   !x:'p. !size:int32. !addend:int64.
     mpdecr_valid
       data_length offset minimum maximum x (ival size)
     ==>
     (&0:int) < ival size
     ==>
     (&0:int) <=
       mpdecr_value pelts offset x (ival size) -
       (&(val addend):int)
     ==>
     writable x = T
     ==>
     minimum x <= offset x /\
     offset x < maximum x /\
     (minimum x <= offset x + (&1:int) /\
      offset x + (&1:int) <= maximum x) /\
     mpdecr_shift_continuation
       data_length offset minimum maximum writable zone pelts
       x size addend (pelts x (offset x))`;;

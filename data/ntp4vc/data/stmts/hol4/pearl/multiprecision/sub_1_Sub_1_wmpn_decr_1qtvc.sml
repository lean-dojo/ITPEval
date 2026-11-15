(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_1_Sub_1_wmpn_decr_1qtvc: the verification
  condition for decrementing a positive-length multiprecision integer in
  place by one, including borrow-loop invariants, pointer updates, and memory
  framing. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory wordsTheory;

val mpdecr1_radix_def = Define `
  mpdecr1_radix = (18446744073709551616 : int)`;

val mpdecr1_to_num_def = Define `
  mpdecr1_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val mpdecr1_int32_in_bounds_def = Define `
  mpdecr1_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val mpdecr1_radix_power_def = Define `
  mpdecr1_radix_power (n : int) =
    mpdecr1_radix ** mpdecr1_to_num n`;

val mpdecr1_value_from_def = Define `
  (mpdecr1_value_from
      (pelts : 'p -> int -> word64) (p : 'p) (index : int) 0 =
     (0 : int)) /\
  (mpdecr1_value_from pelts p index (SUC n) =
     &(w2n (pelts p index)) +
       mpdecr1_radix *
         mpdecr1_value_from pelts p (index + (1 : int)) n)`;

val mpdecr1_value_def = Define `
  mpdecr1_value
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (p : 'p)
      (count : int) =
    mpdecr1_value_from pelts p (offset p) (mpdecr1_to_num count)`;

val mpdecr1_valid_def = Define `
  mpdecr1_valid
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (count : int) <=>
    mpdecr1_int32_in_bounds count /\
    (0 : int) <= count /\
    ((0 : int) <= minimum p /\ minimum p <= offset p) /\
    offset p + count <= maximum p /\
    maximum p <= &(data_length p)`;

val mpdecr1_same_pelts_def = Define `
  mpdecr1_same_pelts
      (pelts : 'p -> int -> word64)
      (left : 'p)
      (right : 'p) <=>
    !j : int. pelts left j = pelts right j`;

val mpdecr1_data_eq_def = Define `
  mpdecr1_data_eq
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (left : 'p)
      (right : 'p) <=>
    data_length left = data_length right /\
    mpdecr1_same_pelts pelts left right`;

val mpdecr1_single_update_def = Define `
  mpdecr1_single_update
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (index : int)
      (value : word64) <=>
    !j : int.
      pelts new j =
        if j = index then value else pelts old j`;

val mpdecr1_shifted_pointer_def = Define `
  mpdecr1_shifted_pointer
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (shifted : 'p)
      (base : 'p)
      (amount : int) <=>
    offset shifted = offset base + amount /\
    data_length shifted = data_length base /\
    mpdecr1_same_pelts pelts shifted base /\
    mpdecr1_data_eq data_length pelts shifted base /\
    minimum shifted = minimum base /\
    maximum shifted = maximum base /\
    zone shifted = zone base /\
    writable shifted = writable base`;

val mpdecr1_loop_memory_metadata_def = Define `
  mpdecr1_loop_memory_metadata
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (memory : 'p)
      (old : 'p) <=>
    data_length memory = data_length old /\
    offset memory = offset old /\
    minimum memory = minimum old /\
    maximum memory = maximum old /\
    writable memory = writable old /\
    zone memory = zone old`;

val mpdecr1_loop_pointer_def = Define `
  mpdecr1_loop_pointer
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (pelts : 'p -> int -> word64)
      (pointer : 'p)
      (memory : 'p)
      (index : int) <=>
    offset pointer = offset memory + index /\
    mpdecr1_same_pelts pelts pointer memory /\
    data_length pointer = data_length memory /\
    minimum pointer = minimum memory /\
    maximum pointer = maximum memory`;

val mpdecr1_tail_unchanged_def = Define `
  mpdecr1_tail_unchanged
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (start : int)
      (size : int) <=>
    !j : int.
      start <= j /\ j < size ==>
      pelts new (offset new + j) =
        pelts old (offset new + j)`;

val mpdecr1_frame_def = Define `
  mpdecr1_frame
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (size : int) <=>
    !j : int.
      j < offset new \/ offset new + size <= j ==>
      pelts new j = pelts old j`;

val mpdecr1_initial_invariant_def = Define `
  mpdecr1_initial_invariant
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (pelts : 'p -> int -> word64)
      (pointer : 'p)
      (old : 'p)
      (size : word32) <=>
    (((0 : int) <= (0 : int) /\ (0 : int) <= w2i size) /\
     ~((0w : word32) = size) /\
     offset pointer = offset old + (0 : int) /\
     mpdecr1_same_pelts pelts pointer old /\
     data_length pointer = data_length old /\
     (minimum pointer = minimum old /\
      maximum pointer = maximum old) /\
     ~((1 : int) = (0 : int)) /\
     ((0 : int) <= (1 : int) /\ (1 : int) <= (1 : int)) /\
     writable pointer = T /\
     mpdecr1_value pelts offset old (0 : int) -
         mpdecr1_radix_power (0 : int) * (1 : int) =
       mpdecr1_value pelts offset old (0 : int) - (1 : int))`;

val mpdecr1_loop_invariant_def = Define `
  mpdecr1_loop_invariant
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (pelts : 'p -> int -> word64)
      (old : 'p)
      (size : word32)
      (pointer : 'p)
      (index : word32)
      (last : word64)
      (borrow : word64)
      (memory : 'p) <=>
    ((0 : int) <= w2i index /\ w2i index <= w2i size) /\
    (index = size ==> ~(&(w2n last) = (0 : int))) /\
    mpdecr1_loop_pointer
      data_length offset minimum maximum pelts
      pointer memory (w2i index) /\
    (~(&(w2n last) = (0 : int)) <=>
     &(w2n borrow) = (0 : int)) /\
    ((0 : int) <= &(w2n borrow) /\ &(w2n borrow) <= (1 : int)) /\
    writable pointer = T /\
    mpdecr1_value pelts offset memory (w2i index) -
        mpdecr1_radix_power (w2i index) * &(w2n borrow) =
      mpdecr1_value pelts offset old (w2i index) - (1 : int) /\
    mpdecr1_tail_unchanged
      offset pelts memory old (w2i index) (w2i size) /\
    mpdecr1_frame offset pelts memory old (w2i size)`;

val mpdecr1_final_state_def = Define `
  mpdecr1_final_state
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (memory : 'p)
      (old : 'p)
      (size : word32) <=>
    mpdecr1_value pelts offset memory (w2i size) =
      mpdecr1_value pelts offset old (w2i size) - (1 : int) /\
    mpdecr1_frame offset pelts memory old (w2i size)`;

val mpdecr1_write_metadata_def = Define `
  mpdecr1_write_metadata
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (updated : 'p)
      (post_write : 'p)
      (before_write : 'p) <=>
    mpdecr1_data_eq data_length pelts updated post_write /\
    data_length post_write = data_length before_write /\
    offset updated = offset before_write /\
    minimum updated = minimum before_write /\
    maximum updated = maximum before_write /\
    writable updated = writable before_write /\
    zone updated = zone before_write`;

val mpdecr1_next_loop_invariant_def = Define `
  mpdecr1_next_loop_invariant
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (pelts : 'p -> int -> word64)
      (old : 'p)
      (size : word32)
      (previous_index : word32)
      (last : word64)
      (memory : 'p)
      (next_index : word32)
      (borrow : word64)
      (pointer : 'p) <=>
    ((0 : int) <= w2i size - w2i previous_index /\
     w2i size - w2i next_index <
       w2i size - w2i previous_index) /\
    ((0 : int) <= w2i next_index /\
     w2i next_index <= w2i size) /\
    (next_index = size ==> ~(&(w2n last) = (0 : int))) /\
    mpdecr1_loop_pointer
      data_length offset minimum maximum pelts
      pointer memory (w2i next_index) /\
    (~(&(w2n last) = (0 : int)) <=>
     &(w2n borrow) = (0 : int)) /\
    ((0 : int) <= &(w2n borrow) /\ &(w2n borrow) <= (1 : int)) /\
    writable pointer = T /\
    mpdecr1_value pelts offset memory (w2i next_index) -
        mpdecr1_radix_power (w2i next_index) * &(w2n borrow) =
      mpdecr1_value pelts offset old (w2i next_index) - (1 : int) /\
    mpdecr1_tail_unchanged
      offset pelts memory old (w2i next_index) (w2i size) /\
    mpdecr1_frame offset pelts memory old (w2i size)`;

val mpdecr1_write_continuation_def = Define `
  mpdecr1_write_continuation
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (old : 'p)
      (size : word32)
      (pointer : 'p)
      (memory : 'p)
      (index : word32)
      (last : word64)
      (result : word64)
      (borrow : word64) <=>
    !updated post_write : 'p.
      mpdecr1_write_metadata
        data_length offset minimum maximum writable zone pelts
        updated post_write pointer ==>
      mpdecr1_write_metadata
        data_length offset minimum maximum writable zone pelts
        updated post_write pointer ==>
      mpdecr1_loop_memory_metadata
        data_length offset minimum maximum writable zone
        post_write memory ==>
      mpdecr1_single_update
        pelts updated pointer (offset updated) result ==>
      mpdecr1_int32_in_bounds (w2i index + (1 : int)) /\
      (!next_index : word32.
         w2i next_index = w2i index + (1 : int) ==>
         (minimum updated <= offset updated + (1 : int) /\
          offset updated + (1 : int) <= maximum updated) /\
         (!next_pointer : 'p.
            mpdecr1_shifted_pointer
              data_length offset minimum maximum writable zone pelts
              next_pointer updated (1 : int) ==>
            mpdecr1_next_loop_invariant
              data_length offset minimum maximum writable pelts
              old size index last post_write next_index borrow
              next_pointer))`;

val mpdecr1_after_zero_test_def = Define `
  mpdecr1_after_zero_test
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (old : 'p)
      (size : word32)
      (pointer : 'p)
      (memory : 'p)
      (index : word32)
      (last : word64)
      (result : word64)
      (borrow : word64) <=>
    (minimum pointer <= offset pointer /\
     offset pointer < maximum pointer) /\
    writable pointer = T /\
    mpdecr1_write_continuation
      data_length offset minimum maximum writable zone pelts
      old size pointer memory index last result borrow`;

val mpdecr1_result_continuation_def = Define `
  mpdecr1_result_continuation
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (old : 'p)
      (size : word32)
      (pointer : 'p)
      (memory : 'p)
      (index : word32)
      (current : word64) <=>
    !result : word64.
      &(w2n result) =
        (&(w2n current) - (1 : int)) % mpdecr1_radix ==>
      (!zero_test : bool.
         (((&(w2n current) = &(w2n (0w : word64))) ==>
           zero_test = T) /\
          (zero_test = T ==> current = (0w : word64))) ==>
         if zero_test = T then
           mpdecr1_after_zero_test
             data_length offset minimum maximum writable zone pelts
             old size pointer memory index current result (1w : word64)
         else
           mpdecr1_after_zero_test
             data_length offset minimum maximum writable zone pelts
             old size pointer memory index current result (0w : word64))`;

val mpdecr1_zero_last_branch_def = Define `
  mpdecr1_zero_last_branch
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (old : 'p)
      (size : word32)
      (pointer : 'p)
      (memory : 'p)
      (index : word32) <=>
    (minimum pointer <= offset pointer /\
     offset pointer < maximum pointer) /\
    mpdecr1_result_continuation
      data_length offset minimum maximum writable zone pelts
      old size pointer memory index
      (pelts pointer (offset pointer))`;

val mpdecr1_loop_result_continuation_def = Define `
  mpdecr1_loop_result_continuation
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (old : 'p)
      (size : word32)
      (pointer : 'p)
      (memory : 'p)
      (index : word32)
      (last : word64) <=>
    !zero_test : bool.
      (((&(w2n last) = &(w2n (0w : word64))) ==>
        zero_test = T) /\
       (zero_test = T ==> last = (0w : word64))) ==>
      if zero_test = T then
        mpdecr1_zero_last_branch
          data_length offset minimum maximum writable zone pelts
          old size pointer memory index
      else
        mpdecr1_final_state offset pelts memory old size`;

val mpdecr1_loop_states_def = Define `
  mpdecr1_loop_states
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (old : 'p)
      (size : word32) <=>
    !pointer : 'p.
    !index : word32.
    !last : word64.
    !borrow : word64.
    !memory : 'p.
      mpdecr1_loop_memory_metadata
        data_length offset minimum maximum writable zone memory old ==>
      mpdecr1_loop_invariant
        data_length offset minimum maximum writable pelts
        old size pointer index last borrow memory ==>
      mpdecr1_loop_result_continuation
        data_length offset minimum maximum writable zone pelts
        old size pointer memory index last`;

val mpdecr1_initial_continuation_def = Define `
  mpdecr1_initial_continuation
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (old : 'p)
      (size : word32) <=>
    !pointer : 'p.
      mpdecr1_shifted_pointer
        data_length offset minimum maximum writable zone pelts
        pointer old (0 : int) ==>
      mpdecr1_initial_invariant
        data_length offset minimum maximum writable pelts
        pointer old size /\
      mpdecr1_loop_states
        data_length offset minimum maximum writable zone pelts old size`;

val sub_1_Sub_1_wmpn_decr_1_vc =
  ``!data_length : 'p -> num.
    !offset minimum maximum : 'p -> int.
    !writable : 'p -> bool.
    !zone : 'p -> 'z.
    !pelts : 'p -> int -> word64.
    !x : 'p.
    !size : word32.
      mpdecr1_valid
        data_length offset minimum maximum x (w2i size) ==>
      (0 : int) < w2i size ==>
      (0 : int) <=
        mpdecr1_value pelts offset x (w2i size) - (1 : int) ==>
      writable x = T ==>
      minimum x <= offset x + (0 : int) /\
      offset x + (0 : int) <= maximum x /\
      mpdecr1_initial_continuation
        data_length offset minimum maximum writable zone pelts x size``;

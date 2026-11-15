(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/add_1_Add_1_wmpn_incr_1qtvc: the verification
  condition for incrementing a positive-length multiprecision integer in
  place by one, including carry-loop invariants, pointer updates, and memory
  framing. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory wordsTheory;

val mpincr1_radix_def = Define `
  mpincr1_radix = (18446744073709551616 : int)`;

val mpincr1_to_num_def = Define `
  mpincr1_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val mpincr1_int32_in_bounds_def = Define `
  mpincr1_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val mpincr1_radix_power_def = Define `
  mpincr1_radix_power (n : int) =
    mpincr1_radix ** mpincr1_to_num n`;

val mpincr1_value_from_def = Define `
  (mpincr1_value_from
      (pelts : 'p -> int -> word64) (p : 'p) (index : int) 0 =
     (0 : int)) /\
  (mpincr1_value_from pelts p index (SUC n) =
     &(w2n (pelts p index)) +
       mpincr1_radix *
         mpincr1_value_from pelts p (index + (1 : int)) n)`;

val mpincr1_value_def = Define `
  mpincr1_value
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (p : 'p)
      (count : int) =
    mpincr1_value_from pelts p (offset p) (mpincr1_to_num count)`;

val mpincr1_valid_def = Define `
  mpincr1_valid
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (count : int) <=>
    mpincr1_int32_in_bounds count /\
    (0 : int) <= count /\
    ((0 : int) <= minimum p /\ minimum p <= offset p) /\
    offset p + count <= maximum p /\
    maximum p <= &(data_length p)`;

val mpincr1_same_pelts_def = Define `
  mpincr1_same_pelts
      (pelts : 'p -> int -> word64)
      (left : 'p)
      (right : 'p) <=>
    !j : int. pelts left j = pelts right j`;

val mpincr1_data_eq_def = Define `
  mpincr1_data_eq
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (left : 'p)
      (right : 'p) <=>
    data_length left = data_length right /\
    mpincr1_same_pelts pelts left right`;

val mpincr1_single_update_def = Define `
  mpincr1_single_update
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (index : int)
      (value : word64) <=>
    !j : int.
      pelts new j =
        if j = index then value else pelts old j`;

val mpincr1_shifted_pointer_def = Define `
  mpincr1_shifted_pointer
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
    mpincr1_same_pelts pelts shifted base /\
    mpincr1_data_eq data_length pelts shifted base /\
    minimum shifted = minimum base /\
    maximum shifted = maximum base /\
    zone shifted = zone base /\
    writable shifted = writable base`;

val mpincr1_loop_memory_metadata_def = Define `
  mpincr1_loop_memory_metadata
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

val mpincr1_loop_pointer_def = Define `
  mpincr1_loop_pointer
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (pelts : 'p -> int -> word64)
      (pointer : 'p)
      (memory : 'p)
      (index : int) <=>
    offset pointer = offset memory + index /\
    mpincr1_same_pelts pelts pointer memory /\
    data_length pointer = data_length memory /\
    minimum pointer = minimum memory /\
    maximum pointer = maximum memory`;

val mpincr1_tail_unchanged_def = Define `
  mpincr1_tail_unchanged
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

val mpincr1_frame_def = Define `
  mpincr1_frame
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (size : int) <=>
    !j : int.
      j < offset new \/ offset new + size <= j ==>
      pelts new j = pelts old j`;

val mpincr1_initial_invariant_def = Define `
  mpincr1_initial_invariant
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
     mpincr1_same_pelts pelts pointer old /\
     data_length pointer = data_length old /\
     (minimum pointer = minimum old /\
      maximum pointer = maximum old) /\
     ~((1 : int) = (0 : int)) /\
     ((0 : int) <= (1 : int) /\ (1 : int) <= (1 : int)) /\
     writable pointer = T /\
     mpincr1_value pelts offset old (0 : int) +
         mpincr1_radix_power (0 : int) * (1 : int) =
       mpincr1_value pelts offset old (0 : int) + (1 : int))`;

val mpincr1_loop_invariant_def = Define `
  mpincr1_loop_invariant
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
      (carry : word64)
      (result : word64)
      (memory : 'p) <=>
    ((0 : int) <= w2i index /\ w2i index <= w2i size) /\
    (index = size ==> ~(&(w2n result) = (0 : int))) /\
    mpincr1_loop_pointer
      data_length offset minimum maximum pelts
      pointer memory (w2i index) /\
    (~(&(w2n result) = (0 : int)) <=>
     &(w2n carry) = (0 : int)) /\
    ((0 : int) <= &(w2n carry) /\ &(w2n carry) <= (1 : int)) /\
    writable pointer = T /\
    mpincr1_value pelts offset memory (w2i index) +
        mpincr1_radix_power (w2i index) * &(w2n carry) =
      mpincr1_value pelts offset old (w2i index) + (1 : int) /\
    mpincr1_tail_unchanged
      offset pelts memory old (w2i index) (w2i size) /\
    mpincr1_frame offset pelts memory old (w2i size)`;

val mpincr1_final_state_def = Define `
  mpincr1_final_state
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (memory : 'p)
      (old : 'p)
      (size : word32) <=>
    mpincr1_value pelts offset memory (w2i size) =
      mpincr1_value pelts offset old (w2i size) + (1 : int) /\
    mpincr1_frame offset pelts memory old (w2i size)`;

val mpincr1_write_metadata_def = Define `
  mpincr1_write_metadata
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
    mpincr1_data_eq data_length pelts updated post_write /\
    data_length post_write = data_length before_write /\
    offset updated = offset before_write /\
    minimum updated = minimum before_write /\
    maximum updated = maximum before_write /\
    writable updated = writable before_write /\
    zone updated = zone before_write`;

val mpincr1_next_loop_invariant_def = Define `
  mpincr1_next_loop_invariant
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (pelts : 'p -> int -> word64)
      (old : 'p)
      (size : word32)
      (previous_index : word32)
      (result : word64)
      (memory : 'p)
      (next_index : word32)
      (carry : word64)
      (pointer : 'p) <=>
    ((0 : int) <= w2i size - w2i previous_index /\
     w2i size - w2i next_index <
       w2i size - w2i previous_index) /\
    ((0 : int) <= w2i next_index /\
     w2i next_index <= w2i size) /\
    (next_index = size ==> ~(&(w2n result) = (0 : int))) /\
    mpincr1_loop_pointer
      data_length offset minimum maximum pelts
      pointer memory (w2i next_index) /\
    (~(&(w2n result) = (0 : int)) <=>
     &(w2n carry) = (0 : int)) /\
    ((0 : int) <= &(w2n carry) /\ &(w2n carry) <= (1 : int)) /\
    writable pointer = T /\
    mpincr1_value pelts offset memory (w2i next_index) +
        mpincr1_radix_power (w2i next_index) * &(w2n carry) =
      mpincr1_value pelts offset old (w2i next_index) + (1 : int) /\
    mpincr1_tail_unchanged
      offset pelts memory old (w2i next_index) (w2i size) /\
    mpincr1_frame offset pelts memory old (w2i size)`;

val mpincr1_write_continuation_def = Define `
  mpincr1_write_continuation
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
      (result : word64)
      (carry : word64) <=>
    !updated post_write : 'p.
      mpincr1_write_metadata
        data_length offset minimum maximum writable zone pelts
        updated post_write pointer ==>
      mpincr1_write_metadata
        data_length offset minimum maximum writable zone pelts
        updated post_write pointer ==>
      mpincr1_loop_memory_metadata
        data_length offset minimum maximum writable zone
        post_write memory ==>
      mpincr1_single_update
        pelts updated pointer (offset updated) result ==>
      mpincr1_int32_in_bounds (w2i index + (1 : int)) /\
      (!next_index : word32.
         w2i next_index = w2i index + (1 : int) ==>
         (minimum updated <= offset updated + (1 : int) /\
          offset updated + (1 : int) <= maximum updated) /\
         (!next_pointer : 'p.
            mpincr1_shifted_pointer
              data_length offset minimum maximum writable zone pelts
              next_pointer updated (1 : int) ==>
            mpincr1_next_loop_invariant
              data_length offset minimum maximum writable pelts
              old size index result post_write next_index carry
              next_pointer))`;

val mpincr1_after_zero_test_def = Define `
  mpincr1_after_zero_test
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
      (result : word64)
      (carry : word64) <=>
    (minimum pointer <= offset pointer /\
     offset pointer < maximum pointer) /\
    writable pointer = T /\
    mpincr1_write_continuation
      data_length offset minimum maximum writable zone pelts
      old size pointer memory index result carry`;

val mpincr1_result_continuation_def = Define `
  mpincr1_result_continuation
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
    !result : word64.
      &(w2n result) =
        (&(w2n (pelts pointer (offset pointer))) + (1 : int))
          rem mpincr1_radix ==>
      (!zero_test : bool.
         (((&(w2n result) = &(w2n (0w : word64))) ==>
           zero_test = T) /\
          (zero_test = T ==> result = (0w : word64))) ==>
         if zero_test = T then
           mpincr1_after_zero_test
             data_length offset minimum maximum writable zone pelts
             old size pointer memory index result (1w : word64)
         else
           mpincr1_after_zero_test
             data_length offset minimum maximum writable zone pelts
             old size pointer memory index result (0w : word64))`;

val mpincr1_zero_result_branch_def = Define `
  mpincr1_zero_result_branch
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
    mpincr1_result_continuation
      data_length offset minimum maximum writable zone pelts
      old size pointer memory index`;

val mpincr1_loop_result_continuation_def = Define `
  mpincr1_loop_result_continuation
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
      (result : word64) <=>
    !zero_test : bool.
      (((&(w2n result) = &(w2n (0w : word64))) ==>
        zero_test = T) /\
       (zero_test = T ==> result = (0w : word64))) ==>
      if zero_test = T then
        mpincr1_zero_result_branch
          data_length offset minimum maximum writable zone pelts
          old size pointer memory index
      else
        mpincr1_final_state offset pelts memory old size`;

val mpincr1_loop_states_def = Define `
  mpincr1_loop_states
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
    !carry : word64.
    !result : word64.
    !memory : 'p.
      mpincr1_loop_memory_metadata
        data_length offset minimum maximum writable zone memory old ==>
      mpincr1_loop_invariant
        data_length offset minimum maximum writable pelts
        old size pointer index carry result memory ==>
      mpincr1_loop_result_continuation
        data_length offset minimum maximum writable zone pelts
        old size pointer memory index result`;

val mpincr1_initial_continuation_def = Define `
  mpincr1_initial_continuation
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
      mpincr1_shifted_pointer
        data_length offset minimum maximum writable zone pelts
        pointer old (0 : int) ==>
      mpincr1_initial_invariant
        data_length offset minimum maximum writable pelts
        pointer old size /\
      mpincr1_loop_states
        data_length offset minimum maximum writable zone pelts old size`;

val add_1_Add_1_wmpn_incr_1_vc =
  ``!data_length : 'p -> num.
    !offset minimum maximum : 'p -> int.
    !writable : 'p -> bool.
    !zone : 'p -> 'z.
    !pelts : 'p -> int -> word64.
    !x : 'p.
    !size : word32.
      mpincr1_valid
        data_length offset minimum maximum x (w2i size) ==>
      (0 : int) < w2i size ==>
      mpincr1_value pelts offset x (w2i size) + (1 : int) <
        mpincr1_radix_power (w2i size) ==>
      writable x = T ==>
      minimum x <= offset x + (0 : int) /\
      offset x + (0 : int) <= maximum x /\
      mpincr1_initial_continuation
        data_length offset minimum maximum writable zone pelts x size``;

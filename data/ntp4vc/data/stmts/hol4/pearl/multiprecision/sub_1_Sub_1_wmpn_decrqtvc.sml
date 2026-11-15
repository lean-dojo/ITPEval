(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_1_Sub_1_wmpn_decrqtvc: the verification condition
  for subtracting one 64-bit limb from a nonempty multiprecision value in
  place, including borrow-loop invariants, pointer updates, and memory
  framing. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory wordsTheory;

val mpdecr_radix_def = Define `
  mpdecr_radix = (18446744073709551616 : int)`;

val mpdecr_to_num_def = Define `
  mpdecr_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val mpdecr_int32_in_bounds_def = Define `
  mpdecr_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val mpdecr_radix_power_def = Define `
  mpdecr_radix_power (n : int) =
    mpdecr_radix ** mpdecr_to_num n`;

val mpdecr_value_from_def = Define `
  (mpdecr_value_from
      (pelts : 'p -> int -> word64) (p : 'p) (index : int) 0 =
     (0 : int)) /\
  (mpdecr_value_from pelts p index (SUC n) =
     &(w2n (pelts p index)) +
       mpdecr_radix *
         mpdecr_value_from pelts p (index + (1 : int)) n)`;

val mpdecr_value_def = Define `
  mpdecr_value
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (p : 'p)
      (count : int) =
    mpdecr_value_from pelts p (offset p) (mpdecr_to_num count)`;

val mpdecr_valid_def = Define `
  mpdecr_valid
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (count : int) <=>
    mpdecr_int32_in_bounds count /\
    (0 : int) <= count /\
    ((0 : int) <= minimum p /\ minimum p <= offset p) /\
    offset p + count <= maximum p /\
    maximum p <= &(data_length p)`;

val mpdecr_same_pelts_def = Define `
  mpdecr_same_pelts
      (pelts : 'p -> int -> word64)
      (left : 'p)
      (right : 'p) <=>
    !j : int. pelts left j = pelts right j`;

val mpdecr_data_eq_def = Define `
  mpdecr_data_eq
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (left : 'p)
      (right : 'p) <=>
    data_length left = data_length right /\
    mpdecr_same_pelts pelts left right`;

val mpdecr_single_update_def = Define `
  mpdecr_single_update
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (index : int)
      (value : word64) <=>
    !j : int.
      pelts new j =
        if j = index then value else pelts old j`;

val mpdecr_shifted_pointer_def = Define `
  mpdecr_shifted_pointer
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
    mpdecr_same_pelts pelts shifted base /\
    mpdecr_data_eq data_length pelts shifted base /\
    minimum shifted = minimum base /\
    maximum shifted = maximum base /\
    zone shifted = zone base /\
    writable shifted = writable base`;

val mpdecr_snapshot_metadata_def = Define `
  mpdecr_snapshot_metadata
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (new : 'p)
      (old : 'p) <=>
    data_length new = data_length old /\
    offset new = offset old /\
    minimum new = minimum old /\
    maximum new = maximum old /\
    writable new = writable old /\
    zone new = zone old`;

val mpdecr_write_metadata_def = Define `
  mpdecr_write_metadata
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
    mpdecr_data_eq data_length pelts updated post_write /\
    data_length post_write = data_length before_write /\
    offset updated = offset before_write /\
    minimum updated = minimum before_write /\
    maximum updated = maximum before_write /\
    writable updated = writable before_write /\
    zone updated = zone before_write`;

val mpdecr_loop_pointer_def = Define `
  mpdecr_loop_pointer
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (pelts : 'p -> int -> word64)
      (pointer : 'p)
      (memory : 'p)
      (index : int) <=>
    offset pointer = offset memory + index /\
    mpdecr_same_pelts pelts pointer memory /\
    data_length pointer = data_length memory /\
    minimum pointer = minimum memory /\
    maximum pointer = maximum memory`;

val mpdecr_tail_unchanged_def = Define `
  mpdecr_tail_unchanged
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

val mpdecr_frame_def = Define `
  mpdecr_frame
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (size : int) <=>
    !j : int.
      j < offset new \/ offset new + size <= j ==>
      pelts new j = pelts old j`;

val mpdecr_final_state_def = Define `
  mpdecr_final_state
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (memory : 'p)
      (old : 'p)
      (size : word32)
      (addend : word64) <=>
    mpdecr_value pelts offset memory (w2i size) =
      mpdecr_value pelts offset old (w2i size) -
      &(w2n addend) /\
    mpdecr_frame offset pelts memory old (w2i size)`;

val mpdecr_initial_loop_invariant_def = Define `
  mpdecr_initial_loop_invariant
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (pelts : 'p -> int -> word64)
      (pointer : 'p)
      (memory : 'p)
      (old : 'p)
      (size : word32)
      (addend : word64) <=>
    ((1 : int) <= (1 : int) /\ (1 : int) <= w2i size) /\
    mpdecr_loop_pointer
      data_length offset minimum maximum pelts
      pointer memory (1 : int) /\
    ((1w : word32) = size ==>
     &(w2n (1w : word64)) = (0 : int)) /\
    ((0 : int) <= &(w2n (1w : word64)) /\
     &(w2n (1w : word64)) <= (1 : int)) /\
    writable pointer = T /\
    mpdecr_value pelts offset memory (1 : int) -
        mpdecr_radix_power (1 : int) *
          &(w2n (1w : word64)) =
      mpdecr_value pelts offset old (1 : int) -
        &(w2n addend) /\
    mpdecr_tail_unchanged
      offset pelts memory old (1 : int) (w2i size) /\
    mpdecr_frame offset pelts memory old (w2i size)`;

val mpdecr_loop_invariant_def = Define `
  mpdecr_loop_invariant
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (pelts : 'p -> int -> word64)
      (pointer : 'p)
      (index : word32)
      (carry : word64)
      (memory : 'p)
      (old : 'p)
      (size : word32)
      (addend : word64) <=>
    ((1 : int) <= w2i index /\ w2i index <= w2i size) /\
    mpdecr_loop_pointer
      data_length offset minimum maximum pelts
      pointer memory (w2i index) /\
    (index = size ==> &(w2n carry) = (0 : int)) /\
    ((0 : int) <= &(w2n carry) /\
     &(w2n carry) <= (1 : int)) /\
    writable pointer = T /\
    mpdecr_value pelts offset memory (w2i index) -
        mpdecr_radix_power (w2i index) * &(w2n carry) =
      mpdecr_value pelts offset old (w2i index) -
        &(w2n addend) /\
    mpdecr_tail_unchanged
      offset pelts memory old (w2i index) (w2i size) /\
    mpdecr_frame offset pelts memory old (w2i size)`;

val mpdecr_next_loop_invariant_def = Define `
  mpdecr_next_loop_invariant
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (pelts : 'p -> int -> word64)
      (pointer : 'p)
      (previous_index : word32)
      (next_index : word32)
      (carry : word64)
      (memory : 'p)
      (old : 'p)
      (size : word32)
      (addend : word64) <=>
    ((0 : int) <= w2i size - w2i previous_index /\
     w2i size - w2i next_index <
       w2i size - w2i previous_index) /\
    mpdecr_loop_invariant
      data_length offset minimum maximum writable pelts
      pointer next_index carry memory old size addend`;

val mpdecr_after_index_increment_def = Define `
  mpdecr_after_index_increment
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (updated : 'p)
      (post_write : 'p)
      (old : 'p)
      (index : word32)
      (size : word32)
      (carry : word64)
      (addend : word64)
      (old_limb : word64) <=>
    mpdecr_int32_in_bounds (w2i index + (1 : int)) /\
    (!next_index : word32.
       w2i next_index = w2i index + (1 : int) ==>
       (minimum updated <= offset updated + (1 : int) /\
        offset updated + (1 : int) <= maximum updated) /\
       (!pointer : 'p.
          mpdecr_shifted_pointer
            data_length offset minimum maximum writable zone pelts
            pointer updated (1 : int) ==>
          (!zero_test : bool.
             (((&(w2n old_limb) =
                &(w2n (0w : word64))) ==>
                zero_test = T) /\
              (zero_test = T ==> old_limb = (0w : word64))) ==>
             if ~(zero_test = T) then
               mpdecr_final_state
                 offset pelts post_write old size addend
             else
               mpdecr_next_loop_invariant
                 data_length offset minimum maximum writable pelts
                 pointer index next_index carry post_write old
                 size addend)))`;

val mpdecr_second_write_continuation_def = Define `
  mpdecr_second_write_continuation
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (pointer : 'p)
      (memory : 'p)
      (old : 'p)
      (index : word32)
      (size : word32)
      (carry : word64)
      (addend : word64)
      (result : word64) <=>
    !updated post_write : 'p.
      mpdecr_write_metadata
        data_length offset minimum maximum writable zone pelts
        updated post_write pointer ==>
      mpdecr_write_metadata
        data_length offset minimum maximum writable zone pelts
        updated post_write pointer ==>
      mpdecr_snapshot_metadata
        data_length offset minimum maximum writable zone
        post_write memory ==>
      mpdecr_single_update
        pelts updated pointer (offset updated) result ==>
      mpdecr_after_index_increment
        data_length offset minimum maximum writable zone pelts
        updated post_write old index size carry addend
        (pelts pointer (offset pointer))`;

val mpdecr_second_result_continuation_def = Define `
  mpdecr_second_result_continuation
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (pointer : 'p)
      (memory : 'p)
      (old : 'p)
      (index : word32)
      (size : word32)
      (carry : word64)
      (addend : word64) <=>
    (minimum pointer <= offset pointer /\
     offset pointer < maximum pointer) /\
    (!result : word64.
       &(w2n result) =
         (&(w2n (pelts pointer (offset pointer))) - (1 : int)) %
           mpdecr_radix ==>
       ((minimum pointer <= offset pointer /\
         offset pointer < maximum pointer) /\
        writable pointer = T) /\
       mpdecr_second_write_continuation
         data_length offset minimum maximum writable zone pelts
         pointer memory old index size carry addend result)`;

val mpdecr_loop_continuation_def = Define `
  mpdecr_loop_continuation
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (pointer : 'p)
      (memory : 'p)
      (old : 'p)
      (index : word32)
      (size : word32)
      (carry : word64)
      (addend : word64) <=>
    !zero_test : bool.
      (((&(w2n carry) = &(w2n (0w : word64))) ==>
        zero_test = T) /\
       (zero_test = T ==> carry = (0w : word64))) ==>
      if ~(zero_test = T) then
        mpdecr_second_result_continuation
          data_length offset minimum maximum writable zone pelts
          pointer memory old index size carry addend
      else
        mpdecr_final_state offset pelts memory old size addend`;

val mpdecr_loop_states_def = Define `
  mpdecr_loop_states
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (initial_memory : 'p)
      (old : 'p)
      (size : word32)
      (addend : word64) <=>
    !index : word32.
    !pointer : 'p.
    !carry : word64.
    !memory : 'p.
      mpdecr_snapshot_metadata
        data_length offset minimum maximum writable zone
        memory initial_memory ==>
      mpdecr_loop_invariant
        data_length offset minimum maximum writable pelts
        pointer index carry memory old size addend ==>
      mpdecr_loop_continuation
        data_length offset minimum maximum writable zone pelts
        pointer memory old index size carry addend`;

val mpdecr_borrow_branch_def = Define `
  mpdecr_borrow_branch
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (pointer : 'p)
      (memory : 'p)
      (old : 'p)
      (size : word32)
      (addend : word64) <=>
    mpdecr_initial_loop_invariant
      data_length offset minimum maximum writable pelts
      pointer memory old size addend /\
    mpdecr_loop_states
      data_length offset minimum maximum writable zone pelts
      memory old size addend`;

val mpdecr_first_write_continuation_def = Define `
  mpdecr_first_write_continuation
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (shifted : 'p)
      (old : 'p)
      (size : word32)
      (addend : word64)
      (initial_limb : word64)
      (result : word64) <=>
    !pointer memory : 'p.
      mpdecr_write_metadata
        data_length offset minimum maximum writable zone pelts
        pointer memory shifted ==>
      mpdecr_snapshot_metadata
        data_length offset minimum maximum writable zone memory old ==>
      mpdecr_single_update
        pelts memory old (offset memory) result ==>
      if &(w2n initial_limb) < &(w2n result) then
        mpdecr_borrow_branch
          data_length offset minimum maximum writable zone pelts
          pointer memory old size addend
      else
        mpdecr_final_state offset pelts memory old size addend`;

val mpdecr_first_result_continuation_def = Define `
  mpdecr_first_result_continuation
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (shifted : 'p)
      (old : 'p)
      (size : word32)
      (addend : word64)
      (initial_limb : word64) <=>
    !result : word64.
      &(w2n result) =
        (&(w2n initial_limb) - &(w2n addend)) %
          mpdecr_radix ==>
      ((minimum old <= offset old /\ offset old < maximum old) /\
       writable old = T) /\
      mpdecr_first_write_continuation
        data_length offset minimum maximum writable zone pelts
        shifted old size addend initial_limb result`;

val mpdecr_shift_continuation_def = Define `
  mpdecr_shift_continuation
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (old : 'p)
      (size : word32)
      (addend : word64)
      (initial_limb : word64) <=>
    !shifted : 'p.
      mpdecr_shifted_pointer
        data_length offset minimum maximum writable zone pelts
        shifted old (1 : int) ==>
      mpdecr_first_result_continuation
        data_length offset minimum maximum writable zone pelts
        shifted old size addend initial_limb`;

val sub_1_Sub_1_wmpn_decr_vc =
  ``!data_length : 'p -> num.
    !offset minimum maximum : 'p -> int.
    !writable : 'p -> bool.
    !zone : 'p -> 'z.
    !pelts : 'p -> int -> word64.
    !x : 'p.
    !size : word32.
    !addend : word64.
      mpdecr_valid
        data_length offset minimum maximum x (w2i size) ==>
      (0 : int) < w2i size ==>
      (0 : int) <=
        mpdecr_value pelts offset x (w2i size) -
          &(w2n addend) ==>
      writable x = T ==>
      minimum x <= offset x /\
      offset x < maximum x /\
      (minimum x <= offset x + (1 : int) /\
       offset x + (1 : int) <= maximum x) /\
      mpdecr_shift_continuation
        data_length offset minimum maximum writable zone pelts
        x size addend (pelts x (offset x))``;

(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_1_Sub_1_wmpn_sub_1qtvc: the verification condition
  for subtracting one 64-bit limb from a positive-length multiprecision
  value into a separate output buffer, including borrow propagation, copying
  of remaining limbs, pointer updates, and memory framing. This file contains
  no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory wordsTheory;

val mpsub_radix_def = Define `
  mpsub_radix = (18446744073709551616 : int)`;

val mpsub_to_num_def = Define `
  mpsub_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val mpsub_int32_in_bounds_def = Define `
  mpsub_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val mpsub_radix_power_def = Define `
  mpsub_radix_power (n : int) =
    mpsub_radix ** mpsub_to_num n`;

val mpsub_value_from_def = Define `
  (mpsub_value_from
      (pelts : 'p -> int -> word64) (p : 'p) (index : int) 0 =
     (0 : int)) /\
  (mpsub_value_from pelts p index (SUC n) =
     &(w2n (pelts p index)) +
       mpsub_radix *
         mpsub_value_from pelts p (index + (1 : int)) n)`;

val mpsub_value_def = Define `
  mpsub_value
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (p : 'p)
      (count : int) =
    mpsub_value_from pelts p (offset p) (mpsub_to_num count)`;

val mpsub_valid_def = Define `
  mpsub_valid
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (count : int) <=>
    mpsub_int32_in_bounds count /\
    (0 : int) <= count /\
    ((0 : int) <= minimum p /\ minimum p <= offset p) /\
    offset p + count <= maximum p /\
    maximum p <= &(data_length p)`;

val mpsub_same_snapshot_def = Define `
  mpsub_same_snapshot
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

val mpsub_single_update_def = Define `
  mpsub_single_update
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (index : int)
      (value : word64) <=>
    !j : int.
      pelts new j =
        if j = index then value else pelts old j`;

val mpsub_frame_def = Define `
  mpsub_frame
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (size : int) <=>
    !j : int.
      j < offset new \/ offset new + size <= j ==>
      pelts new j = pelts old j`;

val mpsub_borrow_invariant_def = Define `
  mpsub_borrow_invariant
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (input : 'p)
      (old_output : 'p)
      (index : word32)
      (borrow : word64)
      (size : word32)
      (subtrahend : word64) <=>
    (1 : int) <= w2i index /\
    w2i index <= w2i size /\
    (0 : int) <= &(w2n borrow) /\
    &(w2n borrow) <= (1 : int) /\
    (index = size \/ &(w2n borrow) = (1 : int)) /\
    mpsub_value pelts offset state (w2i index) -
        mpsub_radix_power (w2i index) * &(w2n borrow) =
      mpsub_value pelts offset input (w2i index) -
        &(w2n subtrahend) /\
    mpsub_frame offset pelts state old_output (w2i size)`;

val mpsub_initial_borrow_invariant_def = Define `
  mpsub_initial_borrow_invariant
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (input : 'p)
      (old_output : 'p)
      (size : word32)
      (subtrahend : word64) <=>
    ((1 : int) <= (1 : int) /\ (1 : int) <= w2i size) /\
    ((0 : int) <= &(w2n (1w : word64)) /\
     &(w2n (1w : word64)) <= (1 : int)) /\
    ((1w : word32) = size \/
     &(w2n (1w : word64)) = (1 : int)) /\
    mpsub_value pelts offset state (1 : int) -
        mpsub_radix_power (1 : int) * &(w2n (1w : word64)) =
      mpsub_value pelts offset input (1 : int) -
        &(w2n subtrahend) /\
    mpsub_frame offset pelts state old_output (w2i size)`;

val mpsub_copy_word_invariant_def = Define `
  mpsub_copy_word_invariant
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (input : 'p)
      (old_output : 'p)
      (index : word32)
      (borrow : word64)
      (size : word32)
      (subtrahend : word64) <=>
    (index = size \/ &(w2n borrow) = (0 : int)) /\
    ((0 : int) <= w2i index /\ w2i index <= w2i size) /\
    mpsub_value pelts offset state (w2i index) -
        mpsub_radix_power (w2i index) * &(w2n borrow) =
      mpsub_value pelts offset input (w2i index) -
        &(w2n subtrahend) /\
    mpsub_frame offset pelts state old_output (w2i size)`;

val mpsub_copy_zero_invariant_def = Define `
  mpsub_copy_zero_invariant
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (input : 'p)
      (old_output : 'p)
      (index : word32)
      (size : word32)
      (subtrahend : word64) <=>
    ((0 : int) <= w2i index /\ w2i index <= w2i size) /\
    mpsub_value pelts offset state (w2i index) -
        mpsub_radix_power (w2i index) * (0 : int) =
      mpsub_value pelts offset input (w2i index) -
        &(w2n subtrahend) /\
    mpsub_frame offset pelts state old_output (w2i size)`;

val mpsub_final_word_state_def = Define `
  mpsub_final_word_state
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (input : 'p)
      (old_output : 'p)
      (size : word32)
      (subtrahend : word64)
      (borrow : word64) <=>
    mpsub_value pelts offset state (w2i size) -
        mpsub_radix_power (w2i size) * &(w2n borrow) =
      mpsub_value pelts offset input (w2i size) -
        &(w2n subtrahend) /\
    mpsub_frame offset pelts state old_output (w2i size) /\
    (0 : int) <= &(w2n borrow) /\
    &(w2n borrow) <= (1 : int)`;

val mpsub_final_zero_state_def = Define `
  mpsub_final_zero_state
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (input : 'p)
      (old_output : 'p)
      (size : word32)
      (subtrahend : word64) <=>
    mpsub_value pelts offset state (w2i size) -
        mpsub_radix_power (w2i size) * (0 : int) =
      mpsub_value pelts offset input (w2i size) -
        &(w2n subtrahend) /\
    mpsub_frame offset pelts state old_output (w2i size) /\
    (0 : int) <= (0 : int) /\
    (0 : int) <= (1 : int)`;

val mpsub_after_copy_word_def = Define `
  mpsub_after_copy_word
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (input : 'p)
      (old_output : 'p)
      (previous_index : word32)
      (borrow : word64)
      (size : word32)
      (subtrahend : word64) <=>
    mpsub_int32_in_bounds (w2i previous_index + (1 : int)) /\
    (!next_index : word32.
       w2i next_index = w2i previous_index + (1 : int) ==>
       ((0 : int) <= w2i size - w2i previous_index /\
        w2i size - w2i next_index <
          w2i size - w2i previous_index) /\
       mpsub_copy_word_invariant
         offset pelts state input old_output next_index borrow
         size subtrahend)`;

val mpsub_after_copy_zero_def = Define `
  mpsub_after_copy_zero
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (input : 'p)
      (old_output : 'p)
      (previous_index : word32)
      (size : word32)
      (subtrahend : word64) <=>
    mpsub_int32_in_bounds (w2i previous_index + (1 : int)) /\
    (!next_index : word32.
       w2i next_index = w2i previous_index + (1 : int) ==>
       ((0 : int) <= w2i size - w2i previous_index /\
        w2i size - w2i next_index <
          w2i size - w2i previous_index) /\
       mpsub_copy_zero_invariant
         offset pelts state input old_output next_index
         size subtrahend)`;

val mpsub_copy_iteration_word_def = Define `
  mpsub_copy_iteration_word
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (input : 'p)
      (old_output : 'p)
      (index : word32)
      (borrow : word64)
      (size : word32)
      (subtrahend : word64) <=>
    if w2i index < w2i size then
      (minimum input <= offset input + w2i index /\
       offset input + w2i index < maximum input) /\
      ((minimum state <= offset state + w2i index /\
        offset state + w2i index < maximum state) /\
       writable state = T) /\
      (!next_state : 'p.
         mpsub_same_snapshot
           data_length offset minimum maximum writable zone
           next_state state ==>
         (mpsub_single_update
            pelts next_state state
            (offset next_state + w2i index)
            (pelts input (offset input + w2i index)) /\
          pelts next_state (offset next_state + w2i index) =
            pelts input (offset input + w2i index)) ==>
         mpsub_after_copy_word
           offset pelts next_state input old_output index borrow
           size subtrahend)
    else
      mpsub_final_word_state
        offset pelts state input old_output size subtrahend borrow`;

val mpsub_copy_iteration_zero_def = Define `
  mpsub_copy_iteration_zero
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (input : 'p)
      (old_output : 'p)
      (index : word32)
      (size : word32)
      (subtrahend : word64) <=>
    if w2i index < w2i size then
      (minimum input <= offset input + w2i index /\
       offset input + w2i index < maximum input) /\
      ((minimum state <= offset state + w2i index /\
        offset state + w2i index < maximum state) /\
       writable state = T) /\
      (!next_state : 'p.
         mpsub_same_snapshot
           data_length offset minimum maximum writable zone
           next_state state ==>
         (mpsub_single_update
            pelts next_state state
            (offset next_state + w2i index)
            (pelts input (offset input + w2i index)) /\
          pelts next_state (offset next_state + w2i index) =
            pelts input (offset input + w2i index)) ==>
         mpsub_after_copy_zero
           offset pelts next_state input old_output index
           size subtrahend)
    else
      mpsub_final_zero_state
        offset pelts state input old_output size subtrahend`;

val mpsub_copy_loop_word_def = Define `
  mpsub_copy_loop_word
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (initial_state : 'p)
      (input : 'p)
      (old_output : 'p)
      (borrow : word64)
      (size : word32)
      (subtrahend : word64) <=>
    !index : word32.
    !state : 'p.
      mpsub_same_snapshot
        data_length offset minimum maximum writable zone
        state initial_state ==>
      mpsub_copy_word_invariant
        offset pelts state input old_output index borrow
        size subtrahend ==>
      mpsub_copy_iteration_word
        data_length offset minimum maximum writable zone pelts
        state input old_output index borrow size subtrahend`;

val mpsub_copy_loop_zero_def = Define `
  mpsub_copy_loop_zero
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (initial_state : 'p)
      (input : 'p)
      (old_output : 'p)
      (size : word32)
      (subtrahend : word64) <=>
    !index : word32.
    !state : 'p.
      mpsub_same_snapshot
        data_length offset minimum maximum writable zone
        state initial_state ==>
      mpsub_copy_zero_invariant
        offset pelts state input old_output index size subtrahend ==>
      mpsub_copy_iteration_zero
        data_length offset minimum maximum writable zone pelts
        state input old_output index size subtrahend`;

val mpsub_after_borrow_write_def = Define `
  mpsub_after_borrow_write
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (input : 'p)
      (old_output : 'p)
      (previous_index : word32)
      (borrow : word64)
      (size : word32)
      (subtrahend : word64) <=>
    mpsub_int32_in_bounds (w2i previous_index + (1 : int)) /\
    (!next_index : word32.
       w2i next_index = w2i previous_index + (1 : int) ==>
       (!zero_test : bool.
          (((&(w2n
                 (pelts input
                    (offset input + w2i previous_index))) =
               &(w2n (0w : word64))) ==>
             zero_test = T) /\
           (zero_test = T ==>
             pelts input (offset input + w2i previous_index) =
               (0w : word64))) ==>
          if ~(zero_test = T) then
            (mpsub_copy_word_invariant
               offset pelts state input old_output next_index
               (0w : word64) size subtrahend /\
             mpsub_copy_loop_word
               data_length offset minimum maximum writable zone pelts
               state input old_output (0w : word64)
               size subtrahend)
          else
            ((0 : int) <= w2i size - w2i previous_index /\
             w2i size - w2i next_index <
               w2i size - w2i previous_index) /\
            mpsub_borrow_invariant
              offset pelts state input old_output next_index borrow
              size subtrahend))`;

val mpsub_borrow_iteration_def = Define `
  mpsub_borrow_iteration
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (input : 'p)
      (old_output : 'p)
      (index : word32)
      (borrow : word64)
      (size : word32)
      (subtrahend : word64) <=>
    if w2i index < w2i size then
      (minimum input <= offset input + w2i index /\
       offset input + w2i index < maximum input) /\
      (!result : word64.
         &(w2n result) =
           (&(w2n
                (pelts input (offset input + w2i index))) -
            (1 : int)) % mpsub_radix ==>
         ((minimum state <= offset state + w2i index /\
           offset state + w2i index < maximum state) /\
          writable state = T) /\
         (!next_state : 'p.
            mpsub_same_snapshot
              data_length offset minimum maximum writable zone
              next_state state ==>
            (mpsub_single_update
               pelts next_state state
               (offset next_state + w2i index) result /\
             pelts next_state (offset next_state + w2i index) =
               result) ==>
            mpsub_after_borrow_write
              data_length offset minimum maximum writable zone pelts
              next_state input old_output index borrow
              size subtrahend))
    else
      mpsub_copy_word_invariant
        offset pelts state input old_output index borrow
        size subtrahend /\
      mpsub_copy_loop_word
        data_length offset minimum maximum writable zone pelts
        state input old_output borrow size subtrahend`;

val mpsub_borrow_loop_def = Define `
  mpsub_borrow_loop
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (initial_state : 'p)
      (input : 'p)
      (old_output : 'p)
      (size : word32)
      (subtrahend : word64) <=>
    !index : word32.
    !borrow : word64.
    !state : 'p.
      mpsub_same_snapshot
        data_length offset minimum maximum writable zone
        state initial_state ==>
      mpsub_borrow_invariant
        offset pelts state input old_output index borrow
        size subtrahend ==>
      mpsub_borrow_iteration
        data_length offset minimum maximum writable zone pelts
        state input old_output index borrow size subtrahend`;

val mpsub_initial_borrow_branch_def = Define `
  mpsub_initial_borrow_branch
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (input : 'p)
      (old_output : 'p)
      (size : word32)
      (subtrahend : word64) <=>
    mpsub_initial_borrow_invariant
      offset pelts state input old_output size subtrahend /\
    mpsub_borrow_loop
      data_length offset minimum maximum writable zone pelts
      state input old_output size subtrahend`;

val mpsub_initial_zero_branch_def = Define `
  mpsub_initial_zero_branch
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (input : 'p)
      (old_output : 'p)
      (size : word32)
      (subtrahend : word64) <=>
    mpsub_copy_zero_invariant
      offset pelts state input old_output (1w : word32)
      size subtrahend /\
    mpsub_copy_loop_zero
      data_length offset minimum maximum writable zone pelts
      state input old_output size subtrahend`;

val sub_1_Sub_1_wmpn_sub_1_vc =
  ``!data_length : 'p -> num.
    !offset minimum maximum : 'p -> int.
    !writable : 'p -> bool.
    !zone : 'p -> 'z.
    !pelts : 'p -> int -> word64.
    !x : 'p.
    !sz : word32.
    !r : 'p.
    !y : word64.
      mpsub_valid
        data_length offset minimum maximum x (w2i sz) ==>
      mpsub_valid
        data_length offset minimum maximum r (w2i sz) ==>
      (0 : int) < w2i sz ==>
      writable r = T ==>
      minimum x <= offset x /\
      offset x < maximum x /\
      (let first_limb : word64 = pelts x (offset x)
       in
         !result : word64.
           &(w2n result) =
             (&(w2n first_limb) - &(w2n y)) %
               mpsub_radix ==>
           ((minimum r <= offset r /\ offset r < maximum r) /\
            writable r = T) /\
           (!state : 'p.
              mpsub_same_snapshot
                data_length offset minimum maximum writable zone
                state r ==>
              mpsub_single_update
                pelts state r (offset state) result ==>
              if &(w2n first_limb) < &(w2n y) then
                mpsub_initial_borrow_branch
                  data_length offset minimum maximum writable zone
                  pelts state x r sz y
              else
                mpsub_initial_zero_branch
                  data_length offset minimum maximum writable zone
                  pelts state x r sz y))``;

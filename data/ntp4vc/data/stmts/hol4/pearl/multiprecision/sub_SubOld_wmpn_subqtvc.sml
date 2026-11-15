(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_SubOld_wmpn_subqtvc: the verification condition for
  unequal-length multiprecision subtraction into a separate result pointer,
  including borrow propagation, copying remaining limbs, pointer updates,
  loop invariants, and memory framing. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory wordsTheory;

val mpsub_sep_radix_def = Define `
  mpsub_sep_radix = (18446744073709551616 : int)`;

val mpsub_sep_to_num_def = Define `
  mpsub_sep_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val mpsub_sep_int32_in_bounds_def = Define `
  mpsub_sep_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val mpsub_sep_radix_power_def = Define `
  mpsub_sep_radix_power (n : int) =
    mpsub_sep_radix ** mpsub_sep_to_num n`;

val mpsub_sep_value_from_def = Define `
  (mpsub_sep_value_from
      (pelts : 'p -> int -> word64) (p : 'p) (index : int) 0 =
     (0 : int)) /\
  (mpsub_sep_value_from pelts p index (SUC n) =
     &(w2n (pelts p index)) +
       mpsub_sep_radix *
         mpsub_sep_value_from pelts p (index + (1 : int)) n)`;

val mpsub_sep_value_def = Define `
  mpsub_sep_value
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (p : 'p)
      (count : int) =
    mpsub_sep_value_from
      pelts p (offset p) (mpsub_sep_to_num count)`;

val mpsub_sep_valid_def = Define `
  mpsub_sep_valid
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (count : int) <=>
    mpsub_sep_int32_in_bounds count /\
    (0 : int) <= count /\
    ((0 : int) <= minimum p /\ minimum p <= offset p) /\
    offset p + count <= maximum p /\
    maximum p <= &(data_length p)`;

val mpsub_sep_same_snapshot_def = Define `
  mpsub_sep_same_snapshot
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

val mpsub_sep_single_update_def = Define `
  mpsub_sep_single_update
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (index : int)
      (value : word64) <=>
    !j : int.
      pelts new j =
        if j = index then value else pelts old j`;

val mpsub_sep_frame_def = Define `
  mpsub_sep_frame
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (count : int) <=>
    !j : int.
      j < offset new \/ offset new + count <= j ==>
      pelts new j = pelts old j`;

val mpsub_sep_access_def = Define `
  mpsub_sep_access
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (index : int) <=>
    minimum p <= index /\ index < maximum p`;

val mpsub_sep_borrow_range_def = Define `
  mpsub_sep_borrow_range (borrow : word64) <=>
    (0 : int) <= &(w2n borrow) /\
    &(w2n borrow) <= (1 : int)`;

val mpsub_sep_zero_flag_def = Define `
  mpsub_sep_zero_flag (limb : word64) (flag : bool) <=>
    (&(w2n limb) = &(w2n (0w : word64)) ==> flag = T) /\
    (flag = T ==> limb = (0w : word64))`;

val mpsub_sep_value_equation_def = Define `
  mpsub_sep_value_equation
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (current : 'p)
      (x : 'p)
      (y : 'p)
      (size : int)
      (ysize : int)
      (borrow : word64) <=>
    mpsub_sep_value pelts offset current size -
        mpsub_sep_radix_power size * &(w2n borrow) =
      mpsub_sep_value pelts offset x size -
        mpsub_sep_value pelts offset y ysize`;

val mpsub_sep_initial_postcondition_def = Define `
  mpsub_sep_initial_postcondition
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (current : 'p)
      (borrow : word64) <=>
    mpsub_sep_borrow_range borrow /\
    mpsub_sep_value_equation
      offset pelts current x y (w2i sy) (w2i sy) borrow /\
    mpsub_sep_frame offset pelts current r (w2i sy)`;

val mpsub_sep_final_state_def = Define `
  mpsub_sep_final_state
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (current : 'p)
      (borrow : word64) <=>
    mpsub_sep_value_equation
      offset pelts current x y (w2i sx) (w2i sy) borrow /\
    mpsub_sep_frame offset pelts current r (w2i sx) /\
    mpsub_sep_borrow_range borrow`;

val mpsub_sep_borrow_invariant_def = Define `
  mpsub_sep_borrow_invariant
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (index : word32)
      (borrow : word64)
      (current : 'p) <=>
    w2i sy <= w2i index /\
    w2i index <= w2i sx /\
    mpsub_sep_value_equation
      offset pelts current x y (w2i index) (w2i sy) borrow /\
    mpsub_sep_frame offset pelts current r (w2i sx) /\
    mpsub_sep_borrow_range borrow /\
    (index = sx \/ &(w2n borrow) = (1 : int))`;

val mpsub_sep_copy_invariant_def = Define `
  mpsub_sep_copy_invariant
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (index : word32)
      (borrow : word64)
      (current : 'p) <=>
    w2i sy <= w2i index /\
    w2i index <= w2i sx /\
    (index = sx \/ &(w2n borrow) = (0 : int)) /\
    mpsub_sep_value_equation
      offset pelts current x y (w2i index) (w2i sy) borrow /\
    mpsub_sep_frame offset pelts current r (w2i sx)`;

val mpsub_sep_copy_after_update_def = Define `
  mpsub_sep_copy_after_update
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (index : word32)
      (borrow : word64)
      (updated : 'p) <=>
    mpsub_sep_int32_in_bounds (w2i index + (1 : int)) /\
    (!next : word32.
       w2i next = w2i index + (1 : int) ==>
       ((0 : int) <= w2i sx - w2i index /\
        w2i sx - w2i next < w2i sx - w2i index) /\
       mpsub_sep_copy_invariant
         offset pelts sy sx r x y next borrow updated)`;

val mpsub_sep_copy_step_def = Define `
  mpsub_sep_copy_step
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (index : word32)
      (borrow : word64)
      (current : 'p) <=>
    if w2i index < w2i sx then
      mpsub_sep_access
        minimum maximum x (offset x + w2i index) /\
      (mpsub_sep_access
         minimum maximum current (offset current + w2i index) /\
       writable current = T) /\
      (!updated : 'p.
         mpsub_sep_same_snapshot
           data_length offset minimum maximum writable zone
           updated current ==>
         (mpsub_sep_single_update
            pelts updated current (offset updated + w2i index)
            (pelts x (offset x + w2i index)) /\
          pelts updated (offset updated + w2i index) =
            pelts x (offset x + w2i index)) ==>
         mpsub_sep_copy_after_update
           offset pelts sy sx r x y index borrow updated)
    else
      mpsub_sep_final_state
        offset pelts sy sx r x y current borrow`;

val mpsub_sep_copy_loop_def = Define `
  mpsub_sep_copy_loop
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (borrow : word64)
      (initial : 'p) <=>
    !index : word32.
    !current : 'p.
      mpsub_sep_same_snapshot
        data_length offset minimum maximum writable zone current initial ==>
      mpsub_sep_copy_invariant
        offset pelts sy sx r x y index borrow current ==>
      mpsub_sep_copy_step
        data_length offset minimum maximum writable zone pelts
        sy sx r x y index borrow current`;

val mpsub_sep_copy_phase_def = Define `
  mpsub_sep_copy_phase
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (index : word32)
      (borrow : word64)
      (current : 'p) <=>
    mpsub_sep_copy_invariant
      offset pelts sy sx r x y index borrow current /\
    mpsub_sep_copy_loop
      data_length offset minimum maximum writable zone pelts
      sy sx r x y borrow current`;

val mpsub_sep_borrow_after_increment_def = Define `
  mpsub_sep_borrow_after_increment
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (index : word32)
      (borrow : word64)
      (updated : 'p)
      (next : word32)
      (old_limb : word64) <=>
    !flag : bool.
      mpsub_sep_zero_flag old_limb flag ==>
      if ~(flag = T) then
        mpsub_sep_copy_phase
          data_length offset minimum maximum writable zone pelts
          sy sx r x y next (0w : word64) updated
      else
        ((0 : int) <= w2i sx - w2i index /\
         w2i sx - w2i next < w2i sx - w2i index) /\
        mpsub_sep_borrow_invariant
          offset pelts sy sx r x y next borrow updated`;

val mpsub_sep_borrow_after_update_def = Define `
  mpsub_sep_borrow_after_update
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (index : word32)
      (borrow : word64)
      (updated : 'p)
      (old_limb : word64) <=>
    mpsub_sep_int32_in_bounds (w2i index + (1 : int)) /\
    (!next : word32.
       w2i next = w2i index + (1 : int) ==>
       mpsub_sep_borrow_after_increment
         data_length offset minimum maximum writable zone pelts
         sy sx r x y index borrow updated next old_limb)`;

val mpsub_sep_borrow_step_def = Define `
  mpsub_sep_borrow_step
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (index : word32)
      (borrow : word64)
      (current : 'p) <=>
    if w2i index < w2i sx then
      mpsub_sep_access
        minimum maximum x (offset x + w2i index) /\
      (!result : word64.
         &(w2n result) =
           (&(w2n (pelts x (offset x + w2i index))) -
            (1 : int)) % mpsub_sep_radix ==>
         (mpsub_sep_access
            minimum maximum current (offset current + w2i index) /\
          writable current = T) /\
         (!updated : 'p.
            mpsub_sep_same_snapshot
              data_length offset minimum maximum writable zone
              updated current ==>
            (mpsub_sep_single_update
               pelts updated current
               (offset updated + w2i index) result /\
             pelts updated (offset updated + w2i index) = result) ==>
            mpsub_sep_borrow_after_update
              data_length offset minimum maximum writable zone pelts
              sy sx r x y index borrow updated
              (pelts x (offset x + w2i index))))
    else
      mpsub_sep_copy_phase
        data_length offset minimum maximum writable zone pelts
        sy sx r x y index borrow current`;

val mpsub_sep_borrow_loop_def = Define `
  mpsub_sep_borrow_loop
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (initial : 'p) <=>
    !index : word32.
    !borrow : word64.
    !current : 'p.
      mpsub_sep_same_snapshot
        data_length offset minimum maximum writable zone current initial ==>
      mpsub_sep_borrow_invariant
        offset pelts sy sx r x y index borrow current ==>
      mpsub_sep_borrow_step
        data_length offset minimum maximum writable zone pelts
        sy sx r x y index borrow current`;

val mpsub_sep_borrow_phase_def = Define `
  mpsub_sep_borrow_phase
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (borrow : word64)
      (current : 'p) <=>
    mpsub_sep_borrow_invariant
      offset pelts sy sx r x y sy borrow current /\
    mpsub_sep_borrow_loop
      data_length offset minimum maximum writable zone pelts
      sy sx r x y current`;

val mpsub_sep_after_initial_flag_def = Define `
  mpsub_sep_after_initial_flag
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (borrow : word64)
      (flag : bool)
      (current : 'p) <=>
    if ~(flag = T) then
      mpsub_sep_borrow_phase
        data_length offset minimum maximum writable zone pelts
        sy sx r x y borrow current
    else
      mpsub_sep_copy_phase
        data_length offset minimum maximum writable zone pelts
        sy sx r x y sy borrow current`;

val mpsub_sep_after_initial_def = Define `
  mpsub_sep_after_initial
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (borrow : word64)
      (current : 'p) <=>
    !flag : bool.
      mpsub_sep_zero_flag borrow flag ==>
      mpsub_sep_after_initial_flag
        data_length offset minimum maximum writable zone pelts
        sy sx r x y borrow flag current`;

val sub_SubOld_wmpn_sub_vc =
  ``!data_length : 'p -> num.
    !offset minimum maximum : 'p -> int.
    !writable : 'p -> bool.
    !zone : 'p -> 'z.
    !pelts : 'p -> int -> word64.
    !sy sx : word32.
    !x y r : 'p.
      (0 : int) <= w2i sy ==>
      w2i sy <= w2i sx ==>
      mpsub_sep_valid
        data_length offset minimum maximum x (w2i sx) ==>
      mpsub_sep_valid
        data_length offset minimum maximum y (w2i sy) ==>
      mpsub_sep_valid
        data_length offset minimum maximum r (w2i sx) ==>
      writable r = T ==>
      mpsub_sep_valid
        data_length offset minimum maximum x (w2i sy) /\
      mpsub_sep_valid
        data_length offset minimum maximum y (w2i sy) /\
      mpsub_sep_valid
        data_length offset minimum maximum r (w2i sy) /\
      writable r = T /\
      (!current : 'p.
         mpsub_sep_same_snapshot
           data_length offset minimum maximum writable zone current r ==>
         (!borrow : word64.
            mpsub_sep_initial_postcondition
              offset pelts sy r x y current borrow ==>
            mpsub_sep_after_initial
              data_length offset minimum maximum writable zone pelts
              sy sx r x y borrow current))``;

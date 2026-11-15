(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_SubOld_wmpn_sub_in_placeqtvc: the verification
  condition for in-place unequal-length multiprecision subtraction, including
  borrow propagation, pointer validity, single-limb updates, loop invariants,
  and memory framing. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory wordsTheory;

val mpsubold_radix_def = Define `
  mpsubold_radix = (18446744073709551616 : int)`;

val mpsubold_to_num_def = Define `
  mpsubold_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val mpsubold_int32_in_bounds_def = Define `
  mpsubold_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val mpsubold_radix_power_def = Define `
  mpsubold_radix_power (n : int) =
    mpsubold_radix ** mpsubold_to_num n`;

val mpsubold_value_from_def = Define `
  (mpsubold_value_from
      (pelts : 'p -> int -> word64) (p : 'p) (index : int) 0 =
     (0 : int)) /\
  (mpsubold_value_from pelts p index (SUC n) =
     &(w2n (pelts p index)) +
       mpsubold_radix *
         mpsubold_value_from pelts p (index + (1 : int)) n)`;

val mpsubold_value_def = Define `
  mpsubold_value
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (p : 'p)
      (count : int) =
    mpsubold_value_from pelts p (offset p) (mpsubold_to_num count)`;

val mpsubold_valid_def = Define `
  mpsubold_valid
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (count : int) <=>
    mpsubold_int32_in_bounds count /\
    (0 : int) <= count /\
    ((0 : int) <= minimum p /\ minimum p <= offset p) /\
    offset p + count <= maximum p /\
    maximum p <= &(data_length p)`;

val mpsubold_same_snapshot_def = Define `
  mpsubold_same_snapshot
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

val mpsubold_single_update_def = Define `
  mpsubold_single_update
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (index : int)
      (value : word64) <=>
    !j : int.
      pelts new j =
        if j = index then value else pelts old j`;

val mpsubold_frame_def = Define `
  mpsubold_frame
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (count : int) <=>
    !j : int.
      j < offset new \/ offset new + count <= j ==>
      pelts new j = pelts old j`;

val mpsubold_tail_equal_def = Define `
  mpsubold_tail_equal
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (start : int)
      (size : int) <=>
    !j : int.
      start <= j /\ j < size ==>
      pelts new (offset new + j) = pelts old (offset new + j)`;

val mpsubold_access_def = Define `
  mpsubold_access
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (index : int) <=>
    minimum p <= index /\ index < maximum p`;

val mpsubold_borrow_range_def = Define `
  mpsubold_borrow_range (borrow : word64) <=>
    (0 : int) <= &(w2n borrow) /\
    &(w2n borrow) <= (1 : int)`;

val mpsubold_value_equation_def = Define `
  mpsubold_value_equation
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (current : 'p)
      (old : 'p)
      (y : 'p)
      (size : int)
      (ysize : int)
      (borrow : word64) <=>
    mpsubold_value pelts offset current size -
        mpsubold_radix_power size * &(w2n borrow) =
      mpsubold_value pelts offset old size -
        mpsubold_value pelts offset y ysize`;

val mpsubold_zero_flag_def = Define `
  mpsubold_zero_flag (limb : word64) (flag : bool) <=>
    (&(w2n limb) = &(w2n (0w : word64)) ==> flag = T) /\
    (flag = T ==> limb = (0w : word64))`;

val mpsubold_final_state_def = Define `
  mpsubold_final_state
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (current : 'p)
      (old : 'p)
      (y : 'p)
      (size : int)
      (ysize : int)
      (borrow : word64) <=>
    mpsubold_value_equation
      offset pelts current old y size ysize borrow /\
    mpsubold_borrow_range borrow /\
    mpsubold_frame offset pelts current old size`;

val mpsubold_loop_invariant_def = Define `
  mpsubold_loop_invariant
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (old : 'p)
      (y : 'p)
      (i : word32)
      (borrow : word64)
      (current : 'p) <=>
    w2i sy <= w2i i /\
    w2i i <= w2i sx /\
    mpsubold_value_equation
      offset pelts current old y (w2i i) (w2i sy) borrow /\
    mpsubold_borrow_range borrow /\
    (i = sx \/ &(w2n borrow) = (1 : int)) /\
    mpsubold_tail_equal
      offset pelts current old (w2i i) (w2i sx) /\
    mpsubold_frame offset pelts current old (w2i sx)`;

val mpsubold_after_increment_def = Define `
  mpsubold_after_increment
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (old : 'p)
      (y : 'p)
      (i : word32)
      (borrow : word64)
      (current : 'p)
      (next : word32)
      (flag : bool) <=>
    if ~(flag = T) then
      mpsubold_final_state
        offset pelts current old y (w2i sx) (w2i sy) (0w : word64)
    else
      ((0 : int) <= w2i sx - w2i i /\
       w2i sx - w2i next < w2i sx - w2i i) /\
      (w2i sy <= w2i next /\ w2i next <= w2i sx) /\
      mpsubold_value_equation
        offset pelts current old y (w2i next) (w2i sy) borrow /\
      mpsubold_borrow_range borrow /\
      (next = sx \/ &(w2n borrow) = (1 : int)) /\
      mpsubold_tail_equal
        offset pelts current old (w2i next) (w2i sx) /\
      mpsubold_frame offset pelts current old (w2i sx)`;

val mpsubold_after_write_def = Define `
  mpsubold_after_write
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (old : 'p)
      (y : 'p)
      (i : word32)
      (borrow : word64)
      (current : 'p)
      (old_limb : word64) <=>
    mpsubold_int32_in_bounds (w2i i + (1 : int)) /\
    (!next : word32.
       w2i next = w2i i + (1 : int) ==>
       (!flag : bool.
          mpsubold_zero_flag old_limb flag ==>
          mpsubold_after_increment
            offset pelts sy sx old y i borrow current next flag))`;

val mpsubold_write_step_def = Define `
  mpsubold_write_step
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (old : 'p)
      (y : 'p)
      (i : word32)
      (borrow : word64)
      (current : 'p) <=>
    mpsubold_access
      minimum maximum current (offset current + w2i i) /\
    (!result : word64.
       &(w2n result) =
         (&(w2n (pelts current (offset current + w2i i))) -
          (1 : int)) % mpsubold_radix ==>
       (mpsubold_access
          minimum maximum current (offset current + w2i i) /\
        writable current = T) /\
       (!updated : 'p.
          mpsubold_same_snapshot
            data_length offset minimum maximum writable zone
            updated current ==>
          (mpsubold_single_update
             pelts updated current (offset updated + w2i i) result /\
           pelts updated (offset updated + w2i i) = result) ==>
          mpsubold_after_write
            offset pelts sy sx old y i borrow updated
            (pelts current (offset current + w2i i))))`;

val mpsubold_loop_step_def = Define `
  mpsubold_loop_step
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (old : 'p)
      (y : 'p)
      (i : word32)
      (borrow : word64)
      (current : 'p) <=>
    if w2i i < w2i sx then
      mpsubold_write_step
        data_length offset minimum maximum writable zone pelts
        sy sx old y i borrow current
    else
      mpsubold_final_state
        offset pelts current old y (w2i sx) (w2i sy) borrow`;

val mpsubold_borrow_loop_def = Define `
  mpsubold_borrow_loop
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (old : 'p)
      (y : 'p)
      (initial : 'p) <=>
    !i : word32.
    !borrow : word64.
    !current : 'p.
      mpsubold_same_snapshot
        data_length offset minimum maximum writable zone current initial ==>
      mpsubold_loop_invariant
        offset pelts sy sx old y i borrow current ==>
      mpsubold_loop_step
        data_length offset minimum maximum writable zone pelts
        sy sx old y i borrow current`;

val mpsubold_continue_after_initial_def = Define `
  mpsubold_continue_after_initial
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (old : 'p)
      (y : 'p)
      (current : 'p)
      (borrow : word64) <=>
    ((w2i sy <= w2i sy /\ w2i sy <= w2i sx) /\
     mpsubold_value_equation
       offset pelts current old y (w2i sy) (w2i sy) borrow /\
     mpsubold_borrow_range borrow /\
     (sy = sx \/ &(w2n borrow) = (1 : int)) /\
     mpsubold_tail_equal
       offset pelts current old (w2i sy) (w2i sx) /\
     mpsubold_frame offset pelts current old (w2i sx)) /\
    mpsubold_borrow_loop
      data_length offset minimum maximum writable zone pelts
      sy sx old y current`;

val mpsubold_after_initial_flag_def = Define `
  mpsubold_after_initial_flag
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (old : 'p)
      (y : 'p)
      (current : 'p)
      (borrow : word64)
      (flag : bool) <=>
    if ~(flag = T) then
      mpsubold_continue_after_initial
        data_length offset minimum maximum writable zone pelts
        sy sx old y current borrow
    else
      mpsubold_final_state
        offset pelts current old y (w2i sx) (w2i sy) borrow`;

val mpsubold_after_initial_def = Define `
  mpsubold_after_initial
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (old : 'p)
      (y : 'p)
      (current : 'p)
      (borrow : word64) <=>
    !flag : bool.
      mpsubold_zero_flag borrow flag ==>
      mpsubold_after_initial_flag
        data_length offset minimum maximum writable zone pelts
        sy sx old y current borrow flag`;

val sub_SubOld_wmpn_sub_in_place_vc =
  ``!data_length : 'p -> num.
    !offset minimum maximum : 'p -> int.
    !writable : 'p -> bool.
    !zone : 'p -> 'z.
    !pelts : 'p -> int -> word64.
    !sy sx : word32.
    !x y : 'p.
      (0 : int) <= w2i sy ==>
      w2i sy <= w2i sx ==>
      mpsubold_valid
        data_length offset minimum maximum x (w2i sx) ==>
      mpsubold_valid
        data_length offset minimum maximum y (w2i sy) ==>
      writable x = T ==>
      (0 : int) <= w2i sy /\
      mpsubold_valid
        data_length offset minimum maximum x (w2i sy) /\
      mpsubold_valid
        data_length offset minimum maximum y (w2i sy) /\
      writable x = T /\
      (!current : 'p.
         mpsubold_same_snapshot
           data_length offset minimum maximum writable zone current x ==>
         (!borrow : word64.
            (mpsubold_value_equation
               offset pelts current x y (w2i sy) (w2i sy) borrow /\
             mpsubold_borrow_range borrow /\
             mpsubold_frame offset pelts current x (w2i sy)) ==>
            mpsubold_after_initial
              data_length offset minimum maximum writable zone pelts
              sy sx x y current borrow))``;

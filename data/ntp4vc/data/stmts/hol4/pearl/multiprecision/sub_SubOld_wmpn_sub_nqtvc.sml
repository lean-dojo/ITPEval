(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_SubOld_wmpn_sub_nqtvc: the verification condition
  for equal-length multiprecision subtraction into a separate destination,
  including signed loop-index bounds, borrow propagation, single-limb
  updates, pointer validity, and memory framing. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory wordsTheory;

val mpsubn_sep_radix_def = Define `
  mpsubn_sep_radix = (18446744073709551616 : int)`;

val mpsubn_sep_to_num_def = Define `
  mpsubn_sep_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val mpsubn_sep_int32_in_bounds_def = Define `
  mpsubn_sep_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val mpsubn_sep_radix_power_def = Define `
  mpsubn_sep_radix_power (n : int) =
    mpsubn_sep_radix ** mpsubn_sep_to_num n`;

val mpsubn_sep_value_from_def = Define `
  (mpsubn_sep_value_from
      (pelts : 'p -> int -> word64) (p : 'p) (index : int) 0 =
     (0 : int)) /\
  (mpsubn_sep_value_from pelts p index (SUC n) =
     &(w2n (pelts p index)) +
       mpsubn_sep_radix *
         mpsubn_sep_value_from pelts p (index + (1 : int)) n)`;

val mpsubn_sep_value_def = Define `
  mpsubn_sep_value
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (p : 'p)
      (count : int) =
    mpsubn_sep_value_from
      pelts p (offset p) (mpsubn_sep_to_num count)`;

val mpsubn_sep_valid_def = Define `
  mpsubn_sep_valid
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (count : int) <=>
    mpsubn_sep_int32_in_bounds count /\
    (0 : int) <= count /\
    ((0 : int) <= minimum p /\ minimum p <= offset p) /\
    offset p + count <= maximum p /\
    maximum p <= &(data_length p)`;

val mpsubn_sep_same_snapshot_def = Define `
  mpsubn_sep_same_snapshot
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

val mpsubn_sep_single_update_def = Define `
  mpsubn_sep_single_update
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (index : int)
      (value : word64) <=>
    !j : int.
      pelts new j =
        if j = index then value else pelts old j`;

val mpsubn_sep_frame_def = Define `
  mpsubn_sep_frame
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (count : int) <=>
    !j : int.
      j < offset new \/ offset new + count <= j ==>
      pelts new j = pelts old j`;

val mpsubn_sep_access_def = Define `
  mpsubn_sep_access
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (index : int) <=>
    minimum p <= index /\ index < maximum p`;

val mpsubn_sep_borrow_range_def = Define `
  mpsubn_sep_borrow_range (borrow : word64) <=>
    (0 : int) <= &(w2n borrow) /\
    &(w2n borrow) <= (1 : int)`;

val mpsubn_sep_value_equation_def = Define `
  mpsubn_sep_value_equation
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (current : 'p)
      (x : 'p)
      (y : 'p)
      (count : int)
      (borrow : word64) <=>
    mpsubn_sep_value pelts offset current count -
        mpsubn_sep_radix_power count * &(w2n borrow) =
      mpsubn_sep_value pelts offset x count -
        mpsubn_sep_value pelts offset y count`;

val mpsubn_sep_loop_invariant_def = Define `
  mpsubn_sep_loop_invariant
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (size : word32)
      (initial : 'p)
      (x : 'p)
      (y : 'p)
      (index : word32)
      (borrow : word64)
      (current : 'p) <=>
    (0 : int) <= w2i index /\
    w2i index <= w2i size /\
    mpsubn_sep_value_equation
      offset pelts current x y (w2i index) borrow /\
    mpsubn_sep_frame
      offset pelts current initial (w2i size) /\
    mpsubn_sep_borrow_range borrow`;

val mpsubn_sep_after_write_def = Define `
  mpsubn_sep_after_write
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (size : word32)
      (initial : 'p)
      (x : 'p)
      (y : 'p)
      (index : word32)
      (borrow : word64)
      (updated : 'p) <=>
    mpsubn_sep_int32_in_bounds (w2i index + (1 : int)) /\
    (!next : word32.
       w2i next = w2i index + (1 : int) ==>
       ((0 : int) <= w2i size - w2i index /\
        w2i size - w2i next < w2i size - w2i index) /\
       mpsubn_sep_loop_invariant
         offset pelts size initial x y next borrow updated)`;

val mpsubn_sep_subtraction_step_def = Define `
  mpsubn_sep_subtraction_step
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (size : word32)
      (initial : 'p)
      (x : 'p)
      (y : 'p)
      (index : word32)
      (borrow_in : word64)
      (current : 'p) <=>
    mpsubn_sep_access
      minimum maximum x (offset x + w2i index) /\
    mpsubn_sep_access
      minimum maximum y (offset y + w2i index) /\
    mpsubn_sep_borrow_range borrow_in /\
    (!result borrow_out : word64.
       (&(w2n result) -
          mpsubn_sep_radix * &(w2n borrow_out) =
        &(w2n (pelts x (offset x + w2i index))) -
          &(w2n (pelts y (offset y + w2i index))) -
          &(w2n borrow_in)) /\
       mpsubn_sep_borrow_range borrow_out ==>
       (mpsubn_sep_access
          minimum maximum current (offset current + w2i index) /\
        writable current = T) /\
       (!updated : 'p.
          mpsubn_sep_same_snapshot
            data_length offset minimum maximum writable zone
            updated current ==>
          (mpsubn_sep_single_update
             pelts updated current (offset updated + w2i index) result /\
           pelts updated (offset updated + w2i index) = result) ==>
          mpsubn_sep_after_write
            offset pelts size initial x y
            index borrow_out updated))`;

val mpsubn_sep_final_state_def = Define `
  mpsubn_sep_final_state
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (size : word32)
      (initial : 'p)
      (x : 'p)
      (y : 'p)
      (borrow : word64)
      (current : 'p) <=>
    mpsubn_sep_borrow_range borrow /\
    mpsubn_sep_value_equation
      offset pelts current x y (w2i size) borrow /\
    mpsubn_sep_frame
      offset pelts current initial (w2i size)`;

val mpsubn_sep_loop_step_def = Define `
  mpsubn_sep_loop_step
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (size : word32)
      (initial : 'p)
      (x : 'p)
      (y : 'p)
      (index : word32)
      (borrow : word64)
      (current : 'p) <=>
    if w2i index < w2i size then
      mpsubn_sep_subtraction_step
        data_length offset minimum maximum writable zone pelts
        size initial x y index borrow current
    else
      mpsubn_sep_final_state
        offset pelts size initial x y borrow current`;

val sub_SubOld_wmpn_sub_n_vc =
  ``!data_length : 'p -> num.
    !offset minimum maximum : 'p -> int.
    !writable : 'p -> bool.
    !zone : 'p -> 'z.
    !pelts : 'p -> int -> word64.
    !size : word32.
    !x y r : 'p.
      mpsubn_sep_valid
        data_length offset minimum maximum x (w2i size) ==>
      mpsubn_sep_valid
        data_length offset minimum maximum y (w2i size) ==>
      mpsubn_sep_valid
        data_length offset minimum maximum r (w2i size) ==>
      writable r = T ==>
      ((0 : int) <= (0 : int)) /\
      ((0 : int) <= w2i size) /\
      (mpsubn_sep_value pelts offset r (0 : int) -
         mpsubn_sep_radix_power (0 : int) * (0 : int) =
       mpsubn_sep_value pelts offset x (0 : int) -
         mpsubn_sep_value pelts offset y (0 : int)) /\
      ((0 : int) <= (0 : int)) /\
      ((0 : int) <= (1 : int)) /\
      (!index : word32.
       !borrow : word64.
       !current : 'p.
         mpsubn_sep_same_snapshot
           data_length offset minimum maximum writable zone current r ==>
         mpsubn_sep_loop_invariant
           offset pelts size r x y index borrow current ==>
         mpsubn_sep_loop_step
           data_length offset minimum maximum writable zone pelts
           size r x y index borrow current)``;

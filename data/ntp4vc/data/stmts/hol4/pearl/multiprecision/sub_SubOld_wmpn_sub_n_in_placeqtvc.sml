(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_SubOld_wmpn_sub_n_in_placeqtvc: the loop
  verification condition for equal-length in-place multiprecision
  subtraction, including borrow arithmetic, pointer-state updates, loop
  invariants, and memory framing. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory wordsTheory;

val mpsubn_radix_def = Define `
  mpsubn_radix = (18446744073709551616 : int)`;

val mpsubn_to_num_def = Define `
  mpsubn_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val mpsubn_int32_in_bounds_def = Define `
  mpsubn_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val mpsubn_radix_power_def = Define `
  mpsubn_radix_power (n : int) =
    mpsubn_radix ** mpsubn_to_num n`;

val mpsubn_value_from_def = Define `
  (mpsubn_value_from
      (pelts : 'p -> int -> word64) (p : 'p) (index : int) 0 =
     (0 : int)) /\
  (mpsubn_value_from pelts p index (SUC n) =
     &(w2n (pelts p index)) +
       mpsubn_radix *
         mpsubn_value_from pelts p (index + (1 : int)) n)`;

val mpsubn_value_def = Define `
  mpsubn_value
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (p : 'p)
      (count : int) =
    mpsubn_value_from pelts p (offset p) (mpsubn_to_num count)`;

val mpsubn_valid_def = Define `
  mpsubn_valid
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (count : int) <=>
    mpsubn_int32_in_bounds count /\
    (0 : int) <= count /\
    ((0 : int) <= minimum p /\ minimum p <= offset p) /\
    offset p + count <= maximum p /\
    maximum p <= &(data_length p)`;

val mpsubn_same_snapshot_def = Define `
  mpsubn_same_snapshot
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

val mpsubn_single_update_def = Define `
  mpsubn_single_update
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (index : int)
      (value : word64) <=>
    !j : int.
      pelts new j =
        if j = index then value else pelts old j`;

val mpsubn_frame_def = Define `
  mpsubn_frame
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (count : int) <=>
    !j : int.
      j < offset new \/ offset new + count <= j ==>
      pelts new j = pelts old j`;

val mpsubn_tail_unchanged_def = Define `
  mpsubn_tail_unchanged
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (start : int)
      (finish : int) <=>
    !j : int.
      start <= j /\ j < finish ==>
      pelts new (offset new + j) =
        pelts old (offset new + j)`;

val mpsubn_access_def = Define `
  mpsubn_access
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (index : int) <=>
    minimum p <= index /\ index < maximum p`;

val mpsubn_borrow_range_def = Define `
  mpsubn_borrow_range (borrow : word64) <=>
    (0 : int) <= &(w2n borrow) /\
    &(w2n borrow) <= (1 : int)`;

val mpsubn_value_equation_def = Define `
  mpsubn_value_equation
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (current : 'p)
      (old : 'p)
      (other : 'p)
      (count : int)
      (borrow : word64) <=>
    mpsubn_value pelts offset current count -
        mpsubn_radix_power count * &(w2n borrow) =
      mpsubn_value pelts offset old count -
        mpsubn_value pelts offset other count`;

val mpsubn_loop_invariant_def = Define `
  mpsubn_loop_invariant
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (size : word32)
      (old : 'p)
      (other : 'p)
      (index : word32)
      (borrow : word64)
      (current : 'p) <=>
    (0 : int) <= w2i index /\
    w2i index <= w2i size /\
    mpsubn_value_equation
      offset pelts current old other (w2i index) borrow /\
    mpsubn_borrow_range borrow /\
    mpsubn_tail_unchanged
      offset pelts current old (w2i index) (w2i size) /\
    mpsubn_frame offset pelts current old (w2i size)`;

val mpsubn_sub_with_borrow_def = Define `
  mpsubn_sub_with_borrow
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (current : 'p)
      (other : 'p)
      (index : word32)
      (borrow_in : word64)
      (result : word64)
      (borrow_out : word64) <=>
    &(w2n result) - mpsubn_radix * &(w2n borrow_out) =
      &(w2n (pelts current (offset current + w2i index))) -
      &(w2n (pelts other (offset other + w2i index))) -
      &(w2n borrow_in) /\
    mpsubn_borrow_range borrow_out`;

val mpsubn_next_invariant_def = Define `
  mpsubn_next_invariant
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (size : word32)
      (old : 'p)
      (other : 'p)
      (index : word32)
      (next : word32)
      (borrow : word64)
      (current : 'p) <=>
    ((0 : int) <= w2i size - w2i index /\
     w2i size - w2i next < w2i size - w2i index) /\
    mpsubn_loop_invariant
      offset pelts size old other next borrow current`;

val mpsubn_after_write_def = Define `
  mpsubn_after_write
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (size : word32)
      (old : 'p)
      (other : 'p)
      (index : word32)
      (borrow : word64)
      (current : 'p) <=>
    mpsubn_int32_in_bounds (w2i index + (1 : int)) /\
    (!next : word32.
       w2i next = w2i index + (1 : int) ==>
       mpsubn_next_invariant
         offset pelts size old other index next borrow current)`;

val mpsubn_write_step_def = Define `
  mpsubn_write_step
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (size : word32)
      (old : 'p)
      (other : 'p)
      (index : word32)
      (borrow_in : word64)
      (current : 'p) <=>
    mpsubn_access
      minimum maximum current (offset current + w2i index) /\
    mpsubn_access
      minimum maximum other (offset other + w2i index) /\
    mpsubn_borrow_range borrow_in /\
    (!result borrow_out : word64.
       mpsubn_sub_with_borrow
         offset pelts current other index borrow_in result borrow_out ==>
       (mpsubn_access
          minimum maximum current (offset current + w2i index) /\
        writable current = T) /\
       (!updated : 'p.
          mpsubn_same_snapshot
            data_length offset minimum maximum writable zone
            updated current ==>
          (mpsubn_single_update
             pelts updated current (offset updated + w2i index) result /\
           pelts updated (offset updated + w2i index) = result) ==>
          mpsubn_after_write
            offset pelts size old other index borrow_out updated))`;

val mpsubn_exit_def = Define `
  mpsubn_exit
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (size : word32)
      (old : 'p)
      (other : 'p)
      (borrow : word64)
      (current : 'p) <=>
    mpsubn_value_equation
      offset pelts current old other (w2i size) borrow /\
    mpsubn_borrow_range borrow /\
    mpsubn_frame offset pelts current old (w2i size)`;

val sub_SubOld_wmpn_sub_n_in_place_vc =
  ``!data_length : 'p -> num.
    !offset minimum maximum : 'p -> int.
    !writable : 'p -> bool.
    !zone : 'p -> 'z.
    !pelts : 'p -> int -> word64.
    !size : word32.
    !x y : 'p.
      (0 : int) <= w2i size ==>
      mpsubn_valid
        data_length offset minimum maximum x (w2i size) ==>
      mpsubn_valid
        data_length offset minimum maximum y (w2i size) ==>
      writable x = T ==>
      ((0 : int) <= (0 : int)) /\
      ((0 : int) <= w2i size) /\
      (mpsubn_value pelts offset x (0 : int) -
         mpsubn_radix_power (0 : int) * (0 : int) =
       mpsubn_value pelts offset x (0 : int) -
         mpsubn_value pelts offset y (0 : int)) /\
      ((0 : int) <= (0 : int)) /\
      ((0 : int) <= (1 : int)) /\
      (!index : word32.
       !borrow : word64.
       !current : 'p.
         mpsubn_same_snapshot
           data_length offset minimum maximum writable zone current x ==>
         mpsubn_loop_invariant
           offset pelts size x y index borrow current ==>
         if w2i index < w2i size then
           mpsubn_write_step
             data_length offset minimum maximum writable zone pelts
             size x y index borrow current
         else
           mpsubn_exit
             offset pelts size x y borrow current)``;

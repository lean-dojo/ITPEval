(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/add_AddOld_wmpn_add_n_in_placeqtvc: the loop
  verification condition for equal-length in-place multiprecision addition,
  including carry arithmetic, pointer-state updates, loop invariants, and
  memory framing. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory wordsTheory;

val mpaddn_radix_def = Define `
  mpaddn_radix = (18446744073709551616 : int)`;

val mpaddn_to_num_def = Define `
  mpaddn_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val mpaddn_int32_in_bounds_def = Define `
  mpaddn_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val mpaddn_radix_power_def = Define `
  mpaddn_radix_power (n : int) =
    mpaddn_radix ** mpaddn_to_num n`;

val mpaddn_value_from_def = Define `
  (mpaddn_value_from
      (pelts : 'p -> int -> word64) (p : 'p) (index : int) 0 =
     (0 : int)) /\
  (mpaddn_value_from pelts p index (SUC n) =
     &(w2n (pelts p index)) +
       mpaddn_radix *
         mpaddn_value_from pelts p (index + (1 : int)) n)`;

val mpaddn_value_def = Define `
  mpaddn_value
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (p : 'p)
      (count : int) =
    mpaddn_value_from pelts p (offset p) (mpaddn_to_num count)`;

val mpaddn_valid_def = Define `
  mpaddn_valid
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (count : int) <=>
    mpaddn_int32_in_bounds count /\
    (0 : int) <= count /\
    ((0 : int) <= minimum p /\ minimum p <= offset p) /\
    offset p + count <= maximum p /\
    maximum p <= &(data_length p)`;

val mpaddn_same_snapshot_def = Define `
  mpaddn_same_snapshot
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

val mpaddn_single_update_def = Define `
  mpaddn_single_update
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (index : int)
      (value : word64) <=>
    !j : int.
      pelts new j =
        if j = index then value else pelts old j`;

val mpaddn_frame_def = Define `
  mpaddn_frame
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (count : int) <=>
    !j : int.
      j < offset new \/ offset new + count <= j ==>
      pelts new j = pelts old j`;

val mpaddn_tail_unchanged_def = Define `
  mpaddn_tail_unchanged
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

val mpaddn_access_def = Define `
  mpaddn_access
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (index : int) <=>
    minimum p <= index /\ index < maximum p`;

val mpaddn_carry_range_def = Define `
  mpaddn_carry_range (carry : word64) <=>
    (0 : int) <= &(w2n carry) /\
    &(w2n carry) <= (1 : int)`;

val mpaddn_value_equation_def = Define `
  mpaddn_value_equation
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (current : 'p)
      (old : 'p)
      (other : 'p)
      (count : int)
      (carry : word64) <=>
    mpaddn_value pelts offset current count +
        mpaddn_radix_power count * &(w2n carry) =
      mpaddn_value pelts offset old count +
        mpaddn_value pelts offset other count`;

val mpaddn_loop_invariant_def = Define `
  mpaddn_loop_invariant
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (size : word32)
      (old : 'p)
      (other : 'p)
      (index : word32)
      (carry : word64)
      (current : 'p) <=>
    (0 : int) <= w2i index /\
    w2i index <= w2i size /\
    mpaddn_value_equation
      offset pelts current old other (w2i index) carry /\
    mpaddn_carry_range carry /\
    mpaddn_tail_unchanged
      offset pelts current old (w2i index) (w2i size) /\
    mpaddn_frame offset pelts current old (w2i size)`;

val mpaddn_add_with_carry_def = Define `
  mpaddn_add_with_carry
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (current : 'p)
      (other : 'p)
      (index : word32)
      (carry_in : word64)
      (result : word64)
      (carry_out : word64) <=>
    &(w2n result) + mpaddn_radix * &(w2n carry_out) =
      &(w2n (pelts current (offset current + w2i index))) +
      &(w2n (pelts other (offset other + w2i index))) +
      &(w2n carry_in) /\
    mpaddn_carry_range carry_out`;

val mpaddn_next_invariant_def = Define `
  mpaddn_next_invariant
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (size : word32)
      (old : 'p)
      (other : 'p)
      (index : word32)
      (next : word32)
      (carry : word64)
      (current : 'p) <=>
    ((0 : int) <= w2i size - w2i index /\
     w2i size - w2i next < w2i size - w2i index) /\
    mpaddn_loop_invariant
      offset pelts size old other next carry current`;

val mpaddn_after_write_def = Define `
  mpaddn_after_write
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (size : word32)
      (old : 'p)
      (other : 'p)
      (index : word32)
      (carry : word64)
      (current : 'p) <=>
    mpaddn_int32_in_bounds (w2i index + (1 : int)) /\
    (!next : word32.
       w2i next = w2i index + (1 : int) ==>
       mpaddn_next_invariant
         offset pelts size old other index next carry current)`;

val mpaddn_write_step_def = Define `
  mpaddn_write_step
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
      (carry_in : word64)
      (current : 'p) <=>
    mpaddn_access
      minimum maximum current (offset current + w2i index) /\
    mpaddn_access
      minimum maximum other (offset other + w2i index) /\
    mpaddn_carry_range carry_in /\
    (!result carry_out : word64.
       mpaddn_add_with_carry
         offset pelts current other index carry_in result carry_out ==>
       (mpaddn_access
          minimum maximum current (offset current + w2i index) /\
        writable current = T) /\
       (!updated : 'p.
          mpaddn_same_snapshot
            data_length offset minimum maximum writable zone
            updated current ==>
          (mpaddn_single_update
             pelts updated current (offset updated + w2i index) result /\
           pelts updated (offset updated + w2i index) = result) ==>
          mpaddn_after_write
            offset pelts size old other index carry_out updated))`;

val mpaddn_exit_def = Define `
  mpaddn_exit
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (size : word32)
      (old : 'p)
      (other : 'p)
      (carry : word64)
      (current : 'p) <=>
    mpaddn_carry_range carry /\
    mpaddn_value_equation
      offset pelts current old other (w2i size) carry /\
    mpaddn_frame offset pelts current old (w2i size)`;

val add_AddOld_wmpn_add_n_in_place_vc =
  ``!data_length : 'p -> num.
    !offset minimum maximum : 'p -> int.
    !writable : 'p -> bool.
    !zone : 'p -> 'z.
    !pelts : 'p -> int -> word64.
    !x : 'p.
    !size : word32.
    !y : 'p.
      mpaddn_valid
        data_length offset minimum maximum x (w2i size) ==>
      mpaddn_valid
        data_length offset minimum maximum y (w2i size) ==>
      writable x = T ==>
      ((0 : int) <= (0 : int)) /\
      ((0 : int) <= w2i size) /\
      (mpaddn_value pelts offset x (0 : int) +
         mpaddn_radix_power (0 : int) * (0 : int) =
       mpaddn_value pelts offset x (0 : int) +
         mpaddn_value pelts offset y (0 : int)) /\
      ((0 : int) <= (0 : int)) /\
      ((0 : int) <= (1 : int)) /\
      (!index : word32.
       !carry : word64.
       !current : 'p.
         mpaddn_same_snapshot
           data_length offset minimum maximum writable zone current x ==>
         mpaddn_loop_invariant
           offset pelts size x y index carry current ==>
         if w2i index < w2i size then
           mpaddn_write_step
             data_length offset minimum maximum writable zone pelts
             size x y index carry current
         else
           mpaddn_exit
             offset pelts size x y carry current)``;

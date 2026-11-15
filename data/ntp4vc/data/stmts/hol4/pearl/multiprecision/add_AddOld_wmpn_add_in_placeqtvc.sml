(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/add_AddOld_wmpn_add_in_placeqtvc: the verification
  condition for in-place addition of two multiprecision integers, including
  carry propagation, pointer-state updates, loop invariants, and memory
  framing. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory wordsTheory;

val mpadd_radix_def = Define `
  mpadd_radix = (18446744073709551616 : int)`;

val mpadd_to_num_def = Define `
  mpadd_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val mpadd_int32_in_bounds_def = Define `
  mpadd_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val mpadd_radix_power_def = Define `
  mpadd_radix_power (n : int) =
    mpadd_radix ** mpadd_to_num n`;

val mpadd_value_from_def = Define `
  (mpadd_value_from
      (pelts : 'p -> int -> word64) (p : 'p) (index : int) 0 =
     (0 : int)) /\
  (mpadd_value_from pelts p index (SUC n) =
     &(w2n (pelts p index)) +
       mpadd_radix *
         mpadd_value_from pelts p (index + (1 : int)) n)`;

val mpadd_value_def = Define `
  mpadd_value
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (p : 'p)
      (count : int) =
    mpadd_value_from pelts p (offset p) (mpadd_to_num count)`;

val mpadd_valid_def = Define `
  mpadd_valid
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (count : int) <=>
    mpadd_int32_in_bounds count /\
    (0 : int) <= count /\
    ((0 : int) <= minimum p /\ minimum p <= offset p) /\
    offset p + count <= maximum p /\
    maximum p <= &(data_length p)`;

val mpadd_same_snapshot_def = Define `
  mpadd_same_snapshot
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

val mpadd_single_update_def = Define `
  mpadd_single_update
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (index : int)
      (value : word64) <=>
    !j : int.
      pelts new j =
        if j = index then value else pelts old j`;

val mpadd_frame_def = Define `
  mpadd_frame
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (count : int) <=>
    !j : int.
      j < offset new \/ offset new + count <= j ==>
      pelts new j = pelts old j`;

val mpadd_tail_unchanged_def = Define `
  mpadd_tail_unchanged
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

val mpadd_initial_result_def = Define `
  mpadd_initial_result
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (old : 'p)
      (other : 'p)
      (size : int)
      (carry : word64) <=>
    ((0 : int) <= &(w2n carry) /\
     &(w2n carry) <= (1 : int)) /\
    mpadd_value pelts offset state size +
        mpadd_radix_power size * &(w2n carry) =
      mpadd_value pelts offset old size +
        mpadd_value pelts offset other size /\
    mpadd_frame offset pelts state old size`;

val mpadd_loop_invariant_def = Define `
  mpadd_loop_invariant
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (old : 'p)
      (other : 'p)
      (other_size : int)
      (index : word32)
      (carry : word64)
      (size : word32) <=>
    other_size <= w2i index /\
    w2i index <= w2i size /\
    mpadd_value pelts offset state (w2i index) +
        mpadd_radix_power (w2i index) * &(w2n carry) =
      mpadd_value pelts offset old (w2i index) +
        mpadd_value pelts offset other other_size /\
    ((0 : int) <= &(w2n carry) /\
     &(w2n carry) <= (1 : int)) /\
    (index = size \/ &(w2n carry) = (1 : int)) /\
    mpadd_tail_unchanged
      offset pelts state old (w2i index) (w2i size) /\
    mpadd_frame offset pelts state old (w2i size)`;

val mpadd_final_state_def = Define `
  mpadd_final_state
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (old : 'p)
      (other : 'p)
      (size : word32)
      (other_size : int)
      (carry : int) <=>
    mpadd_value pelts offset state (w2i size) +
        mpadd_radix_power (w2i size) * carry =
      mpadd_value pelts offset old (w2i size) +
        mpadd_value pelts offset other other_size /\
    ((0 : int) <= carry /\ carry <= (1 : int)) /\
    mpadd_frame offset pelts state old (w2i size)`;

val add_AddOld_wmpn_add_in_place_vc =
  ``!data_length : 'p -> num.
    !offset minimum maximum : 'p -> int.
    !writable : 'p -> bool.
    !zone : 'p -> 'z.
    !pelts : 'p -> int -> word64.
    !sy sx : word32.
    !x y : 'p.
      (0 : int) <= w2i sy ==>
      w2i sy <= w2i sx ==>
      mpadd_valid data_length offset minimum maximum x (w2i sx) ==>
      mpadd_valid data_length offset minimum maximum y (w2i sy) ==>
      writable x = T ==>
      mpadd_valid data_length offset minimum maximum x (w2i sy) /\
      mpadd_valid data_length offset minimum maximum y (w2i sy) /\
      writable x = T /\
      (!x1 : 'p.
         mpadd_same_snapshot
           data_length offset minimum maximum writable zone x1 x ==>
         (!o1 : word64.
            mpadd_initial_result
              offset pelts x1 x y (w2i sy) o1 ==>
            (!o2 : bool.
               (((&(w2n o1) = &(w2n (0w : word64))) ==>
                 o2 = T) /\
                (o2 = T ==> o1 = (0w : word64))) ==>
               if ~(o2 = T) then
                 mpadd_loop_invariant
                   offset pelts x1 x y (w2i sy) sy o1 sx /\
                 (!i : word32.
                  !c : word64.
                  !x2 : 'p.
                    mpadd_same_snapshot
                      data_length offset minimum maximum writable zone
                      x2 x1 ==>
                    mpadd_loop_invariant
                      offset pelts x2 x y (w2i sy) i c sx ==>
                    if w2i i < w2i sx then
                      (minimum x2 <= offset x2 + w2i i /\
                       offset x2 + w2i i < maximum x2) /\
                      (!res : word64.
                         &(w2n res) =
                           (&(w2n (pelts x2 (offset x2 + w2i i))) +
                            (1 : int)) rem mpadd_radix ==>
                         ((minimum x2 <= offset x2 + w2i i /\
                           offset x2 + w2i i < maximum x2) /\
                          writable x2 = T) /\
                         (!x3 : 'p.
                            mpadd_same_snapshot
                              data_length offset minimum maximum writable zone
                              x3 x2 ==>
                            (mpadd_single_update
                               pelts x3 x2 (offset x3 + w2i i) res /\
                             pelts x3 (offset x3 + w2i i) = res) ==>
                            mpadd_int32_in_bounds
                              (w2i i + (1 : int)) /\
                            (!o3 : word32.
                               w2i o3 = w2i i + (1 : int) ==>
                               (!o4 : bool.
                                  (((&(w2n res) =
                                       &(w2n (0w : word64))) ==>
                                    o4 = T) /\
                                   (o4 = T ==>
                                    res = (0w : word64))) ==>
                                  if ~(o4 = T) then
                                    mpadd_final_state
                                      offset pelts x3 x y sx (w2i sy)
                                      (&(w2n (0w : word64)))
                                  else
                                    ((0 : int) <= w2i sx - w2i i /\
                                     w2i sx - w2i o3 <
                                       w2i sx - w2i i) /\
                                    mpadd_loop_invariant
                                      offset pelts x3 x y (w2i sy)
                                      o3 c sx))))
                    else
                      mpadd_final_state
                        offset pelts x2 x y sx (w2i sy) (&(w2n c)))
               else
                 mpadd_final_state
                   offset pelts x1 x y sx (w2i sy) (&(w2n o1)))))``;

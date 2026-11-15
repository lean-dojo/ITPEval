(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/add_1_Add_1_wmpn_add_1_in_placeqtvc: the verification
  condition for in-place addition of one 64-bit limb, including pointer
  updates, carry invariants, framing, and loop continuations. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory wordsTheory;

val mpadd1_radix_def = Define `
  mpadd1_radix = (18446744073709551616 : int)`;

val mpadd1_to_num_def = Define `
  mpadd1_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val mpadd1_int32_in_bounds_def = Define `
  mpadd1_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val mpadd1_radix_power_def = Define `
  mpadd1_radix_power (n : int) =
    mpadd1_radix ** mpadd1_to_num n`;

val mpadd1_value_from_def = Define `
  (mpadd1_value_from
      (pelts : 'p -> int -> word64) (p : 'p) (index : int) 0 =
     (0 : int)) /\
  (mpadd1_value_from pelts p index (SUC n) =
     &(w2n (pelts p index)) +
       mpadd1_radix *
         mpadd1_value_from pelts p (index + (1 : int)) n)`;

val mpadd1_value_def = Define `
  mpadd1_value
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (p : 'p)
      (count : int) =
    mpadd1_value_from pelts p (offset p) (mpadd1_to_num count)`;

val mpadd1_valid_def = Define `
  mpadd1_valid
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (count : int) <=>
    mpadd1_int32_in_bounds count /\
    (0 : int) <= count /\
    ((0 : int) <= minimum p /\ minimum p <= offset p) /\
    offset p + count <= maximum p /\
    maximum p <= &(data_length p)`;

val mpadd1_same_snapshot_def = Define `
  mpadd1_same_snapshot
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

val mpadd1_single_update_def = Define `
  mpadd1_single_update
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (index : int)
      (value : word64) <=>
    !j : int.
      pelts new j =
        if j = index then value else pelts old j`;

val mpadd1_frame_def = Define `
  mpadd1_frame
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (count : int) <=>
    !j : int.
      j < offset new \/ offset new + count <= j ==>
      pelts new j = pelts old j`;

val mpadd1_final_state_def = Define `
  mpadd1_final_state
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (old : 'p)
      (size : int)
      (addend : int)
      (carry : int) <=>
    mpadd1_value pelts offset state size +
        mpadd1_radix_power size * carry =
      mpadd1_value pelts offset old size + addend /\
    (0 : int) <= carry /\
    carry <= (1 : int) /\
    mpadd1_frame offset pelts state old size`;

val mpadd1_loop_invariant_def = Define `
  mpadd1_loop_invariant
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (old : 'p)
      (index : word32)
      (carry : word64)
      (size : word32)
      (addend : word64) <=>
    (1 : int) <= w2i index /\
    w2i index <= w2i size /\
    (0 : int) <= &(w2n carry) /\
    &(w2n carry) <= (1 : int) /\
    (&(w2n carry) = (1 : int) \/ index = size) /\
    mpadd1_value pelts offset state (w2i index) +
        mpadd1_radix_power (w2i index) * &(w2n carry) =
      mpadd1_value pelts offset old (w2i index) + &(w2n addend) /\
    mpadd1_frame offset pelts state old (w2i index)`;

val mpadd1_initial_carry_invariant_def = Define `
  mpadd1_initial_carry_invariant
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (old : 'p)
      (size : word32)
      (addend : word64) <=>
    ((1 : int) <= (1 : int) /\ (1 : int) <= w2i size) /\
    ((0 : int) <= &(w2n (1w : word64)) /\
     &(w2n (1w : word64)) <= (1 : int)) /\
    (&(w2n (1w : word64)) = (1 : int) \/
     (1w : word32) = size) /\
    mpadd1_value pelts offset state (1 : int) +
        mpadd1_radix_power (1 : int) * &(w2n (1w : word64)) =
      mpadd1_value pelts offset old (1 : int) + &(w2n addend) /\
    mpadd1_frame offset pelts state old (1 : int)`;

val add_1_Add_1_wmpn_add_1_in_place_vc =
  ``!data_length : 'p -> num.
    !offset minimum maximum : 'p -> int.
    !writable : 'p -> bool.
    !zone : 'p -> 'z.
    !pelts : 'p -> int -> word64.
    !x : 'p.
    !sz : word32.
    !y : word64.
      mpadd1_valid data_length offset minimum maximum x (w2i sz) ==>
      (0 : int) < w2i sz ==>
      writable x = T ==>
      minimum x <= offset x /\
      offset x < maximum x /\
      (let o1 : word64 = pelts x (offset x)
       in
         !res : word64.
           &(w2n res) =
             (&(w2n o1) + &(w2n y)) rem mpadd1_radix ==>
           ((minimum x <= offset x /\ offset x < maximum x) /\
            writable x = T) /\
           (!x1 : 'p.
              mpadd1_same_snapshot
                data_length offset minimum maximum writable zone x1 x ==>
              mpadd1_single_update pelts x1 x (offset x1) res ==>
              if &(w2n res) < &(w2n o1) then
                mpadd1_initial_carry_invariant
                  offset pelts x1 x sz y /\
                (!i : word32.
                 !c : word64.
                 !x2 : 'p.
                   mpadd1_same_snapshot
                     data_length offset minimum maximum writable zone
                     x2 x1 ==>
                   mpadd1_loop_invariant
                     offset pelts x2 x i c sz y ==>
                   if w2i i < w2i sz then
                     (minimum x2 <= offset x2 + w2i i /\
                      offset x2 + w2i i < maximum x2) /\
                     (!res1 : word64.
                        &(w2n res1) =
                          (&(w2n (pelts x2 (offset x2 + w2i i))) +
                           (1 : int)) rem mpadd1_radix ==>
                        ((minimum x2 <= offset x2 + w2i i /\
                          offset x2 + w2i i < maximum x2) /\
                         writable x2 = T) /\
                        (!x3 : 'p.
                           mpadd1_same_snapshot
                             data_length offset minimum maximum writable zone
                             x3 x2 ==>
                           (mpadd1_single_update
                              pelts x3 x2 (offset x3 + w2i i) res1 /\
                            pelts x3 (offset x3 + w2i i) = res1) ==>
                           mpadd1_int32_in_bounds
                             (w2i i + (1 : int)) /\
                           (!o2 : word32.
                              w2i o2 = w2i i + (1 : int) ==>
                              (!o3 : bool.
                                 ((&(w2n res1) =
                                      &(w2n (0w : word64)) ==>
                                    o3 = T) /\
                                  (o3 = T ==>
                                    res1 = (0w : word64))) ==>
                                 if ~(o3 = T) then
                                   mpadd1_final_state
                                     offset pelts x3 x (w2i sz)
                                     (&(w2n y))
                                     (&(w2n (0w : word64)))
                                 else
                                   ((0 : int) <= w2i sz - w2i i /\
                                    w2i sz - w2i o2 <
                                      w2i sz - w2i i) /\
                                   mpadd1_loop_invariant
                                     offset pelts x3 x o2 c sz y))))
                   else
                     mpadd1_final_state
                       offset pelts x2 x (w2i sz)
                       (&(w2n y)) (&(w2n c)))
              else
                mpadd1_final_state
                  offset pelts x1 x (w2i sz) (&(w2n y)) (0 : int)))``;

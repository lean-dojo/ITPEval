(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_1_Sub_1_wmpn_sub_1_in_placeqtvc: the verification
  condition for in-place subtraction of one 64-bit limb, including pointer
  updates, borrow invariants, memory framing, and loop continuations. This
  file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory wordsTheory;

val mpsub1_radix_def = Define `
  mpsub1_radix = (18446744073709551616 : int)`;

val mpsub1_to_num_def = Define `
  mpsub1_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val mpsub1_int32_in_bounds_def = Define `
  mpsub1_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val mpsub1_radix_power_def = Define `
  mpsub1_radix_power (n : int) =
    mpsub1_radix ** mpsub1_to_num n`;

val mpsub1_value_from_def = Define `
  (mpsub1_value_from
      (pelts : 'p -> int -> word64) (p : 'p) (index : int) 0 =
     (0 : int)) /\
  (mpsub1_value_from pelts p index (SUC n) =
     &(w2n (pelts p index)) +
       mpsub1_radix *
         mpsub1_value_from pelts p (index + (1 : int)) n)`;

val mpsub1_value_def = Define `
  mpsub1_value
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (p : 'p)
      (count : int) =
    mpsub1_value_from pelts p (offset p) (mpsub1_to_num count)`;

val mpsub1_valid_def = Define `
  mpsub1_valid
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (count : int) <=>
    mpsub1_int32_in_bounds count /\
    (0 : int) <= count /\
    ((0 : int) <= minimum p /\ minimum p <= offset p) /\
    offset p + count <= maximum p /\
    maximum p <= &(data_length p)`;

val mpsub1_same_snapshot_def = Define `
  mpsub1_same_snapshot
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

val mpsub1_single_update_def = Define `
  mpsub1_single_update
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (index : int)
      (value : word64) <=>
    !j : int.
      pelts new j =
        if j = index then value else pelts old j`;

val mpsub1_frame_def = Define `
  mpsub1_frame
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (count : int) <=>
    !j : int.
      j < offset new \/ offset new + count <= j ==>
      pelts new j = pelts old j`;

val mpsub1_final_state_def = Define `
  mpsub1_final_state
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (old : 'p)
      (size : int)
      (subtrahend : int)
      (borrow : int) <=>
    mpsub1_value pelts offset state size -
        mpsub1_radix_power size * borrow =
      mpsub1_value pelts offset old size - subtrahend /\
    (0 : int) <= borrow /\
    borrow <= (1 : int) /\
    mpsub1_frame offset pelts state old size`;

val mpsub1_loop_invariant_def = Define `
  mpsub1_loop_invariant
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (old : 'p)
      (index : word32)
      (borrow : word64)
      (size : word32)
      (subtrahend : word64) <=>
    (1 : int) <= w2i index /\
    w2i index <= w2i size /\
    (0 : int) <= &(w2n borrow) /\
    &(w2n borrow) <= (1 : int) /\
    (&(w2n borrow) = (1 : int) \/ index = size) /\
    mpsub1_value pelts offset state (w2i index) -
        mpsub1_radix_power (w2i index) * &(w2n borrow) =
      mpsub1_value pelts offset old (w2i index) -
        &(w2n subtrahend) /\
    mpsub1_frame offset pelts state old (w2i index)`;

val mpsub1_initial_borrow_invariant_def = Define `
  mpsub1_initial_borrow_invariant
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (state : 'p)
      (old : 'p)
      (size : word32)
      (subtrahend : word64) <=>
    ((1 : int) <= (1 : int) /\ (1 : int) <= w2i size) /\
    ((0 : int) <= &(w2n (1w : word64)) /\
     &(w2n (1w : word64)) <= (1 : int)) /\
    (&(w2n (1w : word64)) = (1 : int) \/
     (1w : word32) = size) /\
    mpsub1_value pelts offset state (1 : int) -
        mpsub1_radix_power (1 : int) * &(w2n (1w : word64)) =
      mpsub1_value pelts offset old (1 : int) -
        &(w2n subtrahend) /\
    mpsub1_frame offset pelts state old (1 : int)`;

val sub_1_Sub_1_wmpn_sub_1_in_place_vc =
  ``!data_length : 'p -> num.
    !offset minimum maximum : 'p -> int.
    !writable : 'p -> bool.
    !zone : 'p -> 'z.
    !pelts : 'p -> int -> word64.
    !x : 'p.
    !sz : word32.
    !y : word64.
      mpsub1_valid data_length offset minimum maximum x (w2i sz) ==>
      (0 : int) < w2i sz ==>
      writable x = T ==>
      minimum x <= offset x /\
      offset x < maximum x /\
      (let o1 : word64 = pelts x (offset x)
       in
         !res : word64.
           &(w2n res) =
             (&(w2n o1) - &(w2n y)) % mpsub1_radix ==>
           ((minimum x <= offset x /\ offset x < maximum x) /\
            writable x = T) /\
           (!x1 : 'p.
              mpsub1_same_snapshot
                data_length offset minimum maximum writable zone x1 x ==>
              mpsub1_single_update pelts x1 x (offset x1) res ==>
              if &(w2n o1) < &(w2n y) then
                mpsub1_initial_borrow_invariant
                  offset pelts x1 x sz y /\
                (!i : word32.
                 !b : word64.
                 !x2 : 'p.
                   mpsub1_same_snapshot
                     data_length offset minimum maximum writable zone
                     x2 x1 ==>
                   mpsub1_loop_invariant
                     offset pelts x2 x i b sz y ==>
                   if w2i i < w2i sz then
                     (minimum x2 <= offset x2 + w2i i /\
                      offset x2 + w2i i < maximum x2) /\
                     (!res1 : word64.
                        &(w2n res1) =
                          (&(w2n (pelts x2 (offset x2 + w2i i))) -
                           (1 : int)) % mpsub1_radix ==>
                        ((minimum x2 <= offset x2 + w2i i /\
                          offset x2 + w2i i < maximum x2) /\
                         writable x2 = T) /\
                        (!x3 : 'p.
                           mpsub1_same_snapshot
                             data_length offset minimum maximum writable zone
                             x3 x2 ==>
                           (mpsub1_single_update
                              pelts x3 x2 (offset x3 + w2i i) res1 /\
                            pelts x3 (offset x3 + w2i i) = res1) ==>
                           mpsub1_int32_in_bounds
                             (w2i i + (1 : int)) /\
                           (!o2 : word32.
                              w2i o2 = w2i i + (1 : int) ==>
                              (!o3 : bool.
                                 ((&(w2n
                                       (pelts x2
                                          (offset x2 + w2i i))) =
                                      &(w2n (0w : word64)) ==>
                                    o3 = T) /\
                                  (o3 = T ==>
                                    pelts x2 (offset x2 + w2i i) =
                                      (0w : word64))) ==>
                                 if ~(o3 = T) then
                                   mpsub1_final_state
                                     offset pelts x3 x (w2i sz)
                                     (&(w2n y))
                                     (&(w2n (0w : word64)))
                                 else
                                   ((0 : int) <= w2i sz - w2i i /\
                                    w2i sz - w2i o2 <
                                      w2i sz - w2i i) /\
                                   mpsub1_loop_invariant
                                     offset pelts x3 x o2 b sz y))))
                   else
                     mpsub1_final_state
                       offset pelts x2 x (w2i sz)
                       (&(w2n y)) (&(w2n b)))
              else
                mpsub1_final_state
                  offset pelts x1 x (w2i sz) (&(w2n y)) (0 : int)))``;

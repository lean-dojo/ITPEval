(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/hillel_challenge_Unique_uniqueqtvc: the verification condition for
  constructing a duplicate-free integer list with the same elements as the
  input, preserving finite-map membership and prefix uniqueness invariants.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
val _ = load "finite_mapTheory";
open finite_mapTheory integerTheory listTheory pred_setTheory;

val unique_to_num_def = Define `
  unique_to_num (z : int) = if z < 0 then 0 else Num z`;

val unique_get_def = Define `
  unique_get (xs : int list) (z : int) =
    if unique_to_num z < LENGTH xs then
      EL (unique_to_num z) xs
    else
      (0 : int)`;

val unique_mem_def = Define `
  unique_mem (x : int) (a : int list) (i : int) <=>
    ?j : int.
      ((0 : int) <= j /\ j < i) /\
      unique_get a j = x`;

val unique_prefix_distinct_def = Define `
  unique_prefix_distinct (xs : int list) (len : int) <=>
    !i j : int.
      (0 : int) <= i /\ i < j /\ j < len ==>
      ~(unique_get xs i = unique_get xs j)`;

val unique_state_invariant_def = Define `
  unique_state_invariant
      (a : int list)
      (res : int list)
      (h : int |-> unit)
      (i : int)
      (len : int) <=>
    ((0 : int) <= len /\ len <= i) /\
    (!x : int. unique_mem x a i <=> x IN FDOM h) /\
    (!x : int. unique_mem x a i <=> unique_mem x res len) /\
    unique_prefix_distinct res len`;

val unique_update_matches_def = Define `
  unique_update_matches
      (res : int list) (len : int) (value : int) <=>
    LENGTH (LUPDATE value (unique_to_num len) res) = LENGTH res /\
    (\z : int.
       unique_get (LUPDATE value (unique_to_num len) res) z) =
      (\z : int. if z = len then value else unique_get res z)`;

val unique_iteration_step_def = Define `
  unique_iteration_step
      (a : int list)
      (res : int list)
      (h : int |-> unit)
      (i : int)
      (len : int) <=>
    ((0 : int) <= i /\ i < &(LENGTH a)) /\
    if ~(unique_get a i IN FDOM h) then
      ((0 : int) <= i /\ i < &(LENGTH a)) /\
      !h2 : int |-> unit.
        h2 = h |+ (unique_get a i, ()) ==>
        ((0 : int) <= i /\ i < &(LENGTH a)) /\
        let value = unique_get a i in
          ((0 : int) <= len /\ len < &(LENGTH res)) /\
          (unique_update_matches res len value ==>
           unique_state_invariant
             a
             (LUPDATE value (unique_to_num len) res)
             h2
             (i + (1 : int))
             (len + (1 : int)))
    else
      unique_state_invariant a res h (i + (1 : int)) len`;

val unique_result_condition_def = Define `
  unique_result_condition
      (a : int list) (res : int list) (len : int) <=>
    (((0 : int) <= (0 : int) /\
      (0 : int) <= len /\
      (0 : int) + len <= &(LENGTH res)) /\
     !result : int list.
       &(LENGTH result) = len /\
       (!i : int.
          (0 : int) <= i /\ i < len ==>
          unique_get result i =
            unique_get res ((0 : int) + i))
       ==>
       (!x : int.
          unique_mem x result (&(LENGTH result)) <=>
          unique_mem x a (&(LENGTH a))) /\
       unique_prefix_distinct result (&(LENGTH result)))`;

val hillel_challenge_Unique_uniqueqtvc_statement =
  ``!a : int list.
      let n = &(LENGTH a) in
        !h : int |-> unit.
          h = FEMPTY ==>
          (0 : int) <= n /\
          !res : int list.
            ((!i : int.
                (0 : int) <= i /\ i < n ==>
                unique_get res i = (0 : int)) /\
             &(LENGTH res) = n)
            ==>
            let o1 = n - (1 : int) in
              (((0 : int) <= o1 + (1 : int) ==>
                 (((0 : int) <= (0 : int) /\
                   (!x : int.
                      unique_mem x a (0 : int) <=>
                      x IN FDOM h) /\
                   (!x : int.
                      unique_mem x a (0 : int) <=>
                      unique_mem x res (0 : int)) /\
                   unique_prefix_distinct res (0 : int)) /\
                  !len : int.
                  !res1 : int list.
                  !h1 : int |-> unit.
                    LENGTH res1 = LENGTH res ==>
                    ((!i : int.
                        (((0 : int) <= i /\ i <= o1) /\
                         unique_state_invariant a res1 h1 i len)
                        ==>
                        unique_iteration_step a res1 h1 i len) /\
                     (unique_state_invariant
                        a res1 h1 (o1 + (1 : int)) len
                      ==>
                      unique_result_condition a res1 len)))) /\
               (o1 + (1 : int) < (0 : int) ==>
                unique_result_condition a res (0 : int)))``;

(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2017_odd_even_sort_rearranging_Top_odd_even_sortqtvc:
  the verification condition for odd-even sorting an integer array, including
  permutation, parity-indexed ordering invariants, swaps, entropy decrease,
  termination measures, and final sortedness. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory sortingTheory;

val odd_even_sort_to_num_def = Define `
  odd_even_sort_to_num (i : int) =
    if i < (0 : int) then 0 else Num i`;

val odd_even_sort_nth_def = Define `
  odd_even_sort_nth (a : int list) (i : int) =
    if odd_even_sort_to_num i < LENGTH a then
      EL (odd_even_sort_to_num i) a
    else
      (0 : int)`;

val odd_even_sort_exchange_def = Define `
  odd_even_sort_exchange
      (before : int list) (after : int list)
      (i : int) (j : int) <=>
    after =
      LUPDATE
        (odd_even_sort_nth before i)
        (odd_even_sort_to_num j)
        (LUPDATE
          (odd_even_sort_nth before j)
          (odd_even_sort_to_num i)
          before)`;

val odd_even_sort_permut_def = Define `
  odd_even_sort_permut (a : int list) (b : int list) <=>
    PERM a b`;

val odd_even_sort_sorted_def = Define `
  odd_even_sort_sorted (a : int list) <=>
    !i1 i2 : int.
      (0 : int) <= i1 /\ i1 <= i2 /\ i2 < &(LENGTH a) ==>
      odd_even_sort_nth a i1 <= odd_even_sort_nth a i2`;

val odd_even_sort_odd_def = Define `
  odd_even_sort_odd (i : int) <=>
    ?k : int. i = (2 : int) * k + (1 : int)`;

val odd_even_sort_even_def = Define `
  odd_even_sort_even (i : int) <=>
    ?k : int. i = (2 : int) * k`;

val odd_even_sort_array_max_def = Define `
  (odd_even_sort_array_max ([] : int list) = (0 : int)) /\
  (odd_even_sort_array_max (h :: t) =
     if t = [] then h
     else if odd_even_sort_array_max t < h then
       h
     else
       odd_even_sort_array_max t)`;

val odd_even_sort_max_bound_def = Define `
  odd_even_sort_max_bound (a : int list) (m : int) <=>
    !j : int.
      (0 : int) <= j /\ j < &(LENGTH a) ==>
      odd_even_sort_nth a j <= m`;

val odd_even_sort_entropy_from_def = Define `
  (odd_even_sort_entropy_from
      ([] : int list) (m : int) (i : int) = (0 : int)) /\
  (odd_even_sort_entropy_from (x :: xs) m i =
     i * (m - x) +
       odd_even_sort_entropy_from xs m (i + (1 : int)))`;

val odd_even_sort_entropy_def = Define `
  odd_even_sort_entropy (a : int list) (m : int) =
    odd_even_sort_entropy_from a m (0 : int)`;

val odd_even_sort_odd_prefix_def = Define `
  odd_even_sort_odd_prefix (a : int list) (upper : int) <=>
    !j : int.
      (0 : int) <= j /\ j < upper ==>
      odd_even_sort_odd j ==>
      odd_even_sort_nth a j <=
        odd_even_sort_nth a (j + (1 : int))`;

val odd_even_sort_odd_full_def = Define `
  odd_even_sort_odd_full (a : int list) <=>
    !j : int.
      (((0 : int) <= j /\ j < &(LENGTH a) - (1 : int)) /\
       odd_even_sort_odd j) ==>
      odd_even_sort_nth a j <=
        odd_even_sort_nth a (j + (1 : int))`;

val odd_even_sort_even_prefix_def = Define `
  odd_even_sort_even_prefix (a : int list) (upper : int) <=>
    !j : int.
      (((0 : int) <= j /\ j < upper) /\
       odd_even_sort_even j) ==>
      odd_even_sort_nth a j <=
        odd_even_sort_nth a (j + (1 : int))`;

val odd_even_sort_odd_invariant_def = Define `
  odd_even_sort_odd_invariant
      (original : int list) (anchor : int list) (m : int)
      (i : int) (ok : bool) (current : int list) <=>
    odd_even_sort_permut original current /\
    ((0 : int) <= i /\ i <= &(LENGTH current)) /\
    odd_even_sort_odd i /\
    (ok = T ==>
     odd_even_sort_entropy current m =
       odd_even_sort_entropy anchor m) /\
    (ok = T ==> odd_even_sort_odd_prefix current i) /\
    (~(ok = T) ==>
     odd_even_sort_entropy current m <
       odd_even_sort_entropy anchor m)`;

val odd_even_sort_even_invariant_def = Define `
  odd_even_sort_even_invariant
      (original : int list) (anchor : int list) (m : int)
      (i : int) (ok : bool) (current : int list) <=>
    odd_even_sort_permut original current /\
    ((0 : int) <= i /\ i <= &(LENGTH current)) /\
    odd_even_sort_even i /\
    (ok = T ==>
     odd_even_sort_entropy current m =
       odd_even_sort_entropy anchor m) /\
    (ok = T ==> odd_even_sort_odd_full current) /\
    (ok = T ==> odd_even_sort_even_prefix current i) /\
    (~(ok = T) ==>
     odd_even_sort_entropy current m <
       odd_even_sort_entropy anchor m)`;

val odd_even_sort_variant_decrease_def = Define `
  odd_even_sort_variant_decrease
      (before : int list) (after : int list) (i : int) <=>
    (0 : int) <= &(LENGTH before) - i /\
    &(LENGTH after) - (i + (2 : int)) <
      &(LENGTH before) - i`;

val odd_even_sort_odd_progress_def = Define `
  odd_even_sort_odd_progress
      (original : int list) (anchor : int list) (m : int)
      (before : int list) (i : int) (ok : bool)
      (after : int list) <=>
    odd_even_sort_variant_decrease before after i /\
    odd_even_sort_odd_invariant
      original anchor m (i + (2 : int)) ok after`;

val odd_even_sort_even_progress_def = Define `
  odd_even_sort_even_progress
      (original : int list) (anchor : int list) (m : int)
      (before : int list) (i : int) (ok : bool)
      (after : int list) <=>
    odd_even_sort_variant_decrease before after i /\
    odd_even_sort_even_invariant
      original anchor m (i + (2 : int)) ok after`;

val odd_even_sort_even_exit_def = Define `
  odd_even_sort_even_exit
      (original : int list) (anchor : int list) (m : int)
      (outer_ok : bool) (ok : bool) (current : int list) <=>
    (0 : int) <=
      odd_even_sort_entropy anchor m +
        (if outer_ok = T then (0 : int) else (1 : int)) /\
    odd_even_sort_entropy current m +
        (if ok = T then (0 : int) else (1 : int)) <
      odd_even_sort_entropy anchor m +
        (if outer_ok = T then (0 : int) else (1 : int)) /\
    odd_even_sort_permut original current /\
    (ok = T ==> odd_even_sort_sorted current)`;

val odd_even_sort_even_comparison_def = Define `
  odd_even_sort_even_comparison
      (original : int list) (anchor : int list) (m : int)
      (i : int) (ok : bool) (current : int list) <=>
    let o1 = i + (1 : int)
    in
      ((0 : int) <= o1 /\ o1 < &(LENGTH current)) /\
      ((0 : int) <= i /\ i < &(LENGTH current)) /\
      if odd_even_sort_nth current o1 <
          odd_even_sort_nth current i then
        let o2 = i + (1 : int)
        in
          (odd_even_sort_nth current o2 <
             odd_even_sort_nth current i /\
           (0 : int) <= i /\ i < o2 /\
           o2 < &(LENGTH current)) /\
          (!after : int list.
             LENGTH after = LENGTH current ==>
             odd_even_sort_exchange current after i o2 /\
             odd_even_sort_entropy after m <
               odd_even_sort_entropy current m ==>
             odd_even_sort_even_progress
               original anchor m current i F after)
      else
        odd_even_sort_even_progress
          original anchor m current i ok current`;

val odd_even_sort_even_iteration_def = Define `
  odd_even_sort_even_iteration
      (original : int list) (anchor : int list) (m : int)
      (outer_ok : bool) (i : int) (ok : bool)
      (current : int list) <=>
    if i < &(LENGTH current) - (1 : int) then
      odd_even_sort_even_comparison
        original anchor m i ok current
    else
      odd_even_sort_even_exit
        original anchor m outer_ok ok current`;

val odd_even_sort_even_loop_def = Define `
  odd_even_sort_even_loop
      (original : int list) (anchor : int list) (m : int)
      (outer_ok : bool) (initial : int list) <=>
    !i : int. !ok : bool. !current : int list.
      LENGTH current = LENGTH initial ==>
      odd_even_sort_even_invariant
        original anchor m i ok current ==>
      odd_even_sort_even_iteration
        original anchor m outer_ok i ok current`;

val odd_even_sort_even_phase_def = Define `
  odd_even_sort_even_phase
      (original : int list) (anchor : int list) (m : int)
      (outer_ok : bool) (initial_ok : bool)
      (current : int list) <=>
    odd_even_sort_even_invariant
      original anchor m (0 : int) initial_ok current /\
    odd_even_sort_even_loop
      original anchor m outer_ok current`;

val odd_even_sort_odd_comparison_def = Define `
  odd_even_sort_odd_comparison
      (original : int list) (anchor : int list) (m : int)
      (i : int) (ok : bool) (current : int list) <=>
    let o1 = i + (1 : int)
    in
      ((0 : int) <= o1 /\ o1 < &(LENGTH current)) /\
      ((0 : int) <= i /\ i < &(LENGTH current)) /\
      if odd_even_sort_nth current o1 <
          odd_even_sort_nth current i then
        let o2 = i + (1 : int)
        in
          (odd_even_sort_nth current o2 <
             odd_even_sort_nth current i /\
           (0 : int) <= i /\ i < o2 /\
           o2 < &(LENGTH current)) /\
          (!after : int list.
             LENGTH after = LENGTH current ==>
             odd_even_sort_exchange current after i o2 /\
             odd_even_sort_entropy after m <
               odd_even_sort_entropy current m ==>
             odd_even_sort_odd_progress
               original anchor m current i F after)
      else
        odd_even_sort_odd_progress
          original anchor m current i ok current`;

val odd_even_sort_odd_iteration_def = Define `
  odd_even_sort_odd_iteration
      (original : int list) (anchor : int list) (m : int)
      (outer_ok : bool) (i : int) (ok : bool)
      (current : int list) <=>
    if i < &(LENGTH current) - (1 : int) then
      odd_even_sort_odd_comparison
        original anchor m i ok current
    else
      odd_even_sort_even_phase
        original anchor m outer_ok ok current`;

val odd_even_sort_odd_loop_def = Define `
  odd_even_sort_odd_loop
      (original : int list) (anchor : int list) (m : int)
      (outer_ok : bool) <=>
    !i : int. !ok : bool. !current : int list.
      LENGTH current = LENGTH anchor ==>
      odd_even_sort_odd_invariant
        original anchor m i ok current ==>
      odd_even_sort_odd_iteration
        original anchor m outer_ok i ok current`;

val odd_even_sort_initial_odd_def = Define `
  odd_even_sort_initial_odd
      (original : int list) (current : int list) (m : int) <=>
    odd_even_sort_permut original current /\
    ((0 : int) <= (1 : int) /\
     (1 : int) <= &(LENGTH current)) /\
    odd_even_sort_odd (1 : int) /\
    odd_even_sort_odd_prefix current (1 : int) /\
    (~T ==>
     odd_even_sort_entropy current m <
       odd_even_sort_entropy current m)`;

val odd_even_sort_outer_body_def = Define `
  odd_even_sort_outer_body
      (original : int list) (m : int)
      (ok : bool) (current : int list) <=>
    if ~(ok = T) then
      odd_even_sort_initial_odd original current m /\
      odd_even_sort_odd_loop original current m ok
    else
      odd_even_sort_sorted current /\
      odd_even_sort_permut original current`;

val verifythis_2017_odd_even_sort_rearranging_Top_odd_even_sortqtvc_statement =
  ``!a : int list.
      (0 : int) < &(LENGTH a) ==>
      let m = odd_even_sort_array_max a
      in
        odd_even_sort_max_bound a m ==>
        odd_even_sort_permut a a /\
        (!ok : bool. !a1 : int list.
           LENGTH a1 = LENGTH a ==>
           odd_even_sort_permut a a1 /\
           (ok = T ==> odd_even_sort_sorted a1) ==>
           odd_even_sort_outer_body a m ok a1)``;

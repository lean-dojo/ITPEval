(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/knuth_prime_numbers_PrimeNumbers_prime_numbersqtvc: the integer-list
  verification condition for constructing an initial segment of the prime
  numbers by testing successive odd candidates and recording the next prime.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory primeTheory;

val kpn_to_num_def = Define `
  kpn_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val kpn_nth_def = Define `
  kpn_nth (values : int list) (index : int) =
    if (0 : int) <= index /\ kpn_to_num index < LENGTH values
    then EL (kpn_to_num index) values
    else (0 : int)`;

val kpn_set_def = Define `
  kpn_set (values : int list) (index : int) (value : int) =
    if (0 : int) <= index /\ kpn_to_num index < LENGTH values
    then LUPDATE value (kpn_to_num index) values
    else values`;

val kpn_update_law_def = Define `
  kpn_update_law
    (new_values : int list) (old_values : int list)
    (index : int) (value : int) <=>
    !argument : int.
      kpn_nth new_values argument =
      if argument = index
      then value
      else kpn_nth old_values argument`;

val kpn_prime_def = Define `
  kpn_prime (value : int) <=>
    prime (kpn_to_num value)`;

val kpn_odd_def = Define `
  kpn_odd (value : int) <=>
    ?k : int. value = (2 : int) * k + (1 : int)`;

val kpn_no_prime_in_def = Define `
  kpn_no_prime_in (lower : int) (upper : int) <=>
    !value : int.
      lower < value /\ value < upper ==>
      ~kpn_prime value`;

val kpn_first_primes_def = Define `
  kpn_first_primes (p : int -> int) (upper : int) <=>
    p (0 : int) = (2 : int) /\
    (!i j : int.
       (0 : int) <= i /\ i < j /\ j < upper ==>
       p i < p j) /\
    (!i : int.
       (0 : int) <= i /\ i < upper ==>
       kpn_prime (p i)) /\
    (!i : int.
       (0 : int) <= i /\ i < upper - (1 : int) ==>
       kpn_no_prime_in (p i) (p (i + (1 : int))))`;

val kpn_index_bound_def = Define `
  kpn_index_bound (values : int list) (index : int) <=>
    (0 : int) <= index /\ index < &(LENGTH values)`;

val kpn_last_value_def = Define `
  kpn_last_value (values : int list) (upper : int) =
    kpn_nth values (upper - (1 : int))`;

val kpn_candidate_range_def = Define `
  kpn_candidate_range
    (values : int list) (upper : int) (candidate : int) <=>
    kpn_last_value values upper < candidate /\
    candidate < (2 : int) * kpn_last_value values upper`;

val kpn_search_state_def = Define `
  kpn_search_state
    (values : int list) (upper : int) (candidate : int) <=>
    kpn_first_primes (kpn_nth values) upper /\
    kpn_candidate_range values upper candidate /\
    kpn_odd candidate /\
    kpn_no_prime_in
      (kpn_last_value values upper) candidate`;

val kpn_no_divisor_before_def = Define `
  kpn_no_divisor_before
    (values : int list) (bound : int) (candidate : int) <=>
    !i : int.
      (0 : int) <= i /\ i < bound ==>
      ~(?q : int. candidate = kpn_nth values i * q)`;

val kpn_j_invariant_def = Define `
  kpn_j_invariant
    (values : int list) (upper : int) (candidate : int)
    (last_index : int) <=>
    ((2 : int) <= upper /\ upper <= last_index) /\
    kpn_search_state values upper candidate`;

val kpn_k_invariant_def = Define `
  kpn_k_invariant
    (values : int list) (upper : int) (candidate : int)
    (divisor_index : int) <=>
    ((1 : int) <= divisor_index /\ divisor_index < upper) /\
    kpn_search_state values upper candidate /\
    kpn_no_divisor_before values divisor_index candidate`;

val kpn_candidate_prime_def = Define `
  kpn_candidate_prime
    (values : int list) (upper : int) (candidate : int) <=>
    kpn_last_value values upper < candidate /\
    kpn_prime candidate /\
    kpn_no_prime_in
      (kpn_last_value values upper) candidate`;

val kpn_reset_state_def = Define `
  kpn_reset_state
    (values : int list) (upper : int) (candidate : int) <=>
    ((1 : int) <= (1 : int) /\ (1 : int) < upper) /\
    kpn_search_state values upper candidate /\
    kpn_no_divisor_before values (1 : int) candidate`;

val kpn_divisible_decrease_def = Define `
  kpn_divisible_decrease
    (values : int list) (upper : int) (candidate : int)
    (divisor_index : int) <=>
    let distance =
      (2 : int) * kpn_last_value values upper - candidate
    in
    let next_distance =
      (2 : int) * kpn_last_value values upper -
      (candidate + (2 : int))
    in
      ((0 : int) <= distance /\ next_distance < distance) \/
      (distance = next_distance /\
       (0 : int) <= upper - divisor_index /\
       upper - (1 : int) < upper - divisor_index)`;

val kpn_advance_decrease_def = Define `
  kpn_advance_decrease
    (values : int list) (upper : int) (candidate : int)
    (divisor_index : int) <=>
    let distance =
      (2 : int) * kpn_last_value values upper - candidate
    in
    let next_index = divisor_index + (1 : int)
    in
      ((0 : int) <= distance /\ distance < distance) \/
      ((0 : int) <= upper - divisor_index /\
       upper - next_index < upper - divisor_index)`;

val kpn_divisible_branch_def = Define `
  kpn_divisible_branch
    (values : int list) (upper : int) (candidate : int)
    (divisor_index : int) <=>
    kpn_divisible_decrease
      values upper candidate divisor_index /\
    kpn_reset_state
      values upper (candidate + (2 : int))`;

val kpn_advance_branch_def = Define `
  kpn_advance_branch
    (values : int list) (upper : int) (candidate : int)
    (divisor_index : int) <=>
    let next_index = divisor_index + (1 : int)
    in
      kpn_advance_decrease
        values upper candidate divisor_index /\
      (((1 : int) <= next_index /\ next_index < upper) /\
       kpn_search_state values upper candidate /\
       kpn_no_divisor_before values next_index candidate)`;

val kpn_nondivisible_branch_def = Define `
  kpn_nondivisible_branch
    (values : int list) (upper : int) (candidate : int)
    (divisor_index : int) <=>
    kpn_index_bound values divisor_index /\
    kpn_index_bound values divisor_index /\
    (let divisor = kpn_nth values divisor_index
     in
       ~(divisor = (0 : int)) /\
       if kpn_nth values divisor_index < candidate quot divisor
       then
         kpn_advance_branch
           values upper candidate divisor_index
       else
         kpn_candidate_prime values upper candidate)`;

val kpn_k_branch_def = Define `
  kpn_k_branch
    (values : int list) (upper : int) (candidate : int)
    (divisor_index : int) <=>
    let divisor = kpn_nth values divisor_index
    in
      ~(divisor = (0 : int)) /\
      if candidate rem divisor = (0 : int)
      then
        kpn_divisible_branch
          values upper candidate divisor_index
      else
        kpn_nondivisible_branch
          values upper candidate divisor_index`;

val kpn_k_loop_def = Define `
  kpn_k_loop
    (values : int list) (upper : int) (candidate : int) <=>
    !divisor_index : int.
      kpn_k_invariant values upper candidate divisor_index ==>
      kpn_index_bound values divisor_index /\
      kpn_k_branch values upper candidate divisor_index`;

val kpn_all_k_loops_def = Define `
  kpn_all_k_loops
    (reference_values : int list) (upper : int) <=>
    !candidate : int.
    !values : int list.
      LENGTH values = LENGTH reference_values ==>
      kpn_k_loop values upper candidate`;

val kpn_set_preserves_model_def = Define `
  kpn_set_preserves_model
    (values : int list) (index : int) (value : int) <=>
    LENGTH (kpn_set values index value) = LENGTH values /\
    kpn_update_law
      (kpn_set values index value) values index value`;

val kpn_candidate_insertion_def = Define `
  kpn_candidate_insertion
    (values : int list) (upper : int) <=>
    !candidate : int.
      kpn_candidate_prime values upper candidate ==>
      kpn_index_bound values upper /\
      (kpn_set_preserves_model values upper candidate ==>
       kpn_search_state
         (kpn_set values upper candidate)
         (upper + (1 : int))
         (candidate + (2 : int)))`;

val kpn_j_step_def = Define `
  kpn_j_step
    (values : int list) (upper : int) (candidate : int) <=>
    kpn_all_k_loops values upper /\
    kpn_reset_state values upper candidate /\
    kpn_candidate_insertion values upper`;

val kpn_all_j_steps_def = Define `
  kpn_all_j_steps
    (prepared : int list) (requested_length : int)
    (last_index : int) <=>
    !candidate : int.
    !values : int list.
      LENGTH values = LENGTH prepared ==>
      ((!upper : int.
          kpn_j_invariant
            values upper candidate last_index ==>
          kpn_j_step values upper candidate) /\
       (kpn_search_state
          values (last_index + (1 : int)) candidate ==>
        &(LENGTH values) = requested_length /\
        kpn_first_primes (kpn_nth values) requested_length))`;

val kpn_main_branch_def = Define `
  kpn_main_branch
    (prepared : int list) (requested_length : int)
    (last_index : int) <=>
    kpn_search_state prepared (2 : int) (5 : int) /\
    kpn_all_j_steps prepared requested_length last_index`;

val kpn_small_branch_def = Define `
  kpn_small_branch
    (prepared : int list) (requested_length : int) <=>
    &(LENGTH prepared) = requested_length /\
    kpn_first_primes (kpn_nth prepared) requested_length`;

val kpn_prepared_branches_def = Define `
  kpn_prepared_branches
    (prepared : int list) (requested_length : int) <=>
    let last_index = requested_length - (1 : int)
    in
      (((2 : int) <= last_index + (1 : int) ==>
        kpn_main_branch prepared requested_length last_index) /\
       (last_index + (1 : int) < (2 : int) ==>
        kpn_small_branch prepared requested_length))`;

val kpn_after_first_set_def = Define `
  kpn_after_first_set
    (values : int list) (requested_length : int) <=>
    let after_two = kpn_set values (0 : int) (2 : int)
    in
    let prepared = kpn_set after_two (1 : int) (3 : int)
    in
      kpn_index_bound after_two (1 : int) /\
      (kpn_set_preserves_model after_two (1 : int) (3 : int) ==>
       kpn_prepared_branches prepared requested_length)`;

val kpn_initialize_list_def = Define `
  kpn_initialize_list
    (values : int list) (requested_length : int) <=>
    kpn_index_bound values (0 : int) /\
    (kpn_set_preserves_model values (0 : int) (2 : int) ==>
     kpn_after_first_set values requested_length)`;

val kpn_initial_zero_list_def = Define `
  kpn_initial_zero_list
    (values : int list) (requested_length : int) <=>
    (!i : int.
       (0 : int) <= i /\ i < requested_length ==>
       kpn_nth values i = (0 : int)) /\
    &(LENGTH values) = requested_length`;

val knuth_prime_numbers_PrimeNumbers_prime_numbersqtvc_statement =
  ``(!p : int.
       kpn_prime p ==>
       ~kpn_no_prime_in p ((2 : int) * p))
    ==>
    !requested_length : int.
      (2 : int) <= requested_length ==>
      (0 : int) <= requested_length /\
      !values : int list.
        kpn_initial_zero_list values requested_length ==>
        kpn_initialize_list values requested_length``;

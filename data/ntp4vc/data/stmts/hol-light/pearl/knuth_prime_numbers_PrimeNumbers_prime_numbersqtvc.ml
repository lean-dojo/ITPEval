(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/knuth_prime_numbers_PrimeNumbers_prime_numbersqtvc: the integer-list
  verification condition for constructing an initial segment of the prime
  numbers by testing successive odd candidates and recording the next prime.
  This file contains no proof.
*)

needs "Library/prime.ml";;

let knuth_prime_numbers_nth = new_definition
 `knuth_prime_numbers_nth (values:int list) (position:int) =
    if values = [] then (&0:int)
    else if position < (&0:int) then (&0:int)
    else if num_of_int position < LENGTH values
    then EL (num_of_int position) values
    else (&0:int)`;;

let knuth_prime_numbers_set_nat =
  new_recursive_definition list_RECURSION
   `(!position value:int.
       knuth_prime_numbers_set_nat [] position value = []) /\
    (!head:int.
     !tail:int list.
     !position:num.
     !value:int.
       knuth_prime_numbers_set_nat (CONS head tail) position value =
       if position = 0 then CONS value tail
       else
         CONS head
           (knuth_prime_numbers_set_nat tail (PRE position) value))`;;

let knuth_prime_numbers_set = new_definition
 `knuth_prime_numbers_set (values:int list) (position:int) (value:int) =
    knuth_prime_numbers_set_nat values (num_of_int position) value`;;

let knuth_prime_numbers_update_law = new_definition
 `knuth_prime_numbers_update_law
    (new_values:int list) (old_values:int list)
    (position:int) (value:int) <=>
    !argument:int.
      knuth_prime_numbers_nth new_values argument =
      (if argument = position
       then value
       else knuth_prime_numbers_nth old_values argument)`;;

let knuth_prime_numbers_prime = new_definition
 `knuth_prime_numbers_prime (value:int) <=>
    (&2:int) <= value /\ prime (num_of_int value)`;;

let knuth_prime_numbers_odd = new_definition
 `knuth_prime_numbers_odd (value:int) <=>
    ?k:int. value = (&2:int) * k + (&1:int)`;;

let knuth_prime_numbers_no_prime_in = new_definition
 `knuth_prime_numbers_no_prime_in (lower:int) (upper:int) <=>
    !value:int.
      lower < value /\ value < upper
      ==> ~knuth_prime_numbers_prime value`;;

let knuth_prime_numbers_first_primes = new_definition
 `knuth_prime_numbers_first_primes (p:int->int) (upper:int) <=>
    p (&0:int) = (&2:int) /\
    (!i j:int.
       (&0:int) <= i /\ i < j /\ j < upper
       ==> p i < p j) /\
    (!i:int.
       (&0:int) <= i /\ i < upper
       ==> knuth_prime_numbers_prime (p i)) /\
    (!i:int.
       (&0:int) <= i /\ i < upper - (&1:int)
       ==> knuth_prime_numbers_no_prime_in
             (p i) (p (i + (&1:int))) )`;;

let knuth_prime_numbers_index_bound = new_definition
 `knuth_prime_numbers_index_bound (values:int list) (position:int) <=>
    (&0:int) <= position /\ position < (&(LENGTH values):int)`;;

let knuth_prime_numbers_last_value = new_definition
 `knuth_prime_numbers_last_value (values:int list) (upper:int) =
    knuth_prime_numbers_nth values (upper - (&1:int))`;;

let knuth_prime_numbers_candidate_range = new_definition
 `knuth_prime_numbers_candidate_range
    (values:int list) (upper:int) (candidate:int) <=>
    knuth_prime_numbers_last_value values upper < candidate /\
    candidate <
      (&2:int) * knuth_prime_numbers_last_value values upper`;;

let knuth_prime_numbers_search_state = new_definition
 `knuth_prime_numbers_search_state
    (values:int list) (upper:int) (candidate:int) <=>
    knuth_prime_numbers_first_primes
      (knuth_prime_numbers_nth values) upper /\
    knuth_prime_numbers_candidate_range values upper candidate /\
    knuth_prime_numbers_odd candidate /\
    knuth_prime_numbers_no_prime_in
      (knuth_prime_numbers_last_value values upper) candidate`;;

let knuth_prime_numbers_no_divisor_before = new_definition
 `knuth_prime_numbers_no_divisor_before
    (values:int list) (bound:int) (candidate:int) <=>
    !i:int.
      (&0:int) <= i /\ i < bound
      ==> ~(knuth_prime_numbers_nth values i divides candidate)`;;

let knuth_prime_numbers_j_invariant = new_definition
 `knuth_prime_numbers_j_invariant
    (values:int list) (upper:int) (candidate:int) (last_index:int) <=>
    ((&2:int) <= upper /\ upper <= last_index) /\
    knuth_prime_numbers_search_state values upper candidate`;;

let knuth_prime_numbers_k_invariant = new_definition
 `knuth_prime_numbers_k_invariant
    (values:int list) (upper:int) (candidate:int)
    (divisor_index:int) <=>
    ((&1:int) <= divisor_index /\ divisor_index < upper) /\
    knuth_prime_numbers_search_state values upper candidate /\
    knuth_prime_numbers_no_divisor_before
      values divisor_index candidate`;;

let knuth_prime_numbers_candidate_prime = new_definition
 `knuth_prime_numbers_candidate_prime
    (values:int list) (upper:int) (candidate:int) <=>
    knuth_prime_numbers_last_value values upper < candidate /\
    knuth_prime_numbers_prime candidate /\
    knuth_prime_numbers_no_prime_in
      (knuth_prime_numbers_last_value values upper) candidate`;;

let knuth_prime_numbers_reset_state = new_definition
 `knuth_prime_numbers_reset_state
    (values:int list) (upper:int) (candidate:int) <=>
    ((&1:int) <= (&1:int) /\ (&1:int) < upper) /\
    knuth_prime_numbers_search_state values upper candidate /\
    knuth_prime_numbers_no_divisor_before
      values (&1:int) candidate`;;

let knuth_prime_numbers_cdiv = new_definition
 `knuth_prime_numbers_cdiv (n:int) (d:int) =
    if (&0:int) <= n
    then if (&0:int) <= d then n div d else --(n div --d)
    else if (&0:int) <= d then --(--n div d) else --n div --d`;;

let knuth_prime_numbers_cmod = new_definition
 `knuth_prime_numbers_cmod (n:int) (d:int) =
    n - d * knuth_prime_numbers_cdiv n d`;;

let knuth_prime_numbers_divisible_decrease = new_definition
 `knuth_prime_numbers_divisible_decrease
    (values:int list) (upper:int) (candidate:int)
    (divisor_index:int) <=>
    let distance =
      (&2:int) * knuth_prime_numbers_last_value values upper -
      candidate in
    let next_distance =
      (&2:int) * knuth_prime_numbers_last_value values upper -
      (candidate + (&2:int)) in
    ((&0:int) <= distance /\ next_distance < distance) \/
    (distance = next_distance /\
     (&0:int) <= upper - divisor_index /\
     upper - (&1:int) < upper - divisor_index)`;;

let knuth_prime_numbers_advance_decrease = new_definition
 `knuth_prime_numbers_advance_decrease
    (values:int list) (upper:int) (candidate:int)
    (divisor_index:int) <=>
    let distance =
      (&2:int) * knuth_prime_numbers_last_value values upper -
      candidate in
    let next_index = divisor_index + (&1:int) in
    ((&0:int) <= distance /\ distance < distance) \/
    ((&0:int) <= upper - divisor_index /\
     upper - next_index < upper - divisor_index)`;;

let knuth_prime_numbers_divisible_branch = new_definition
 `knuth_prime_numbers_divisible_branch
    (values:int list) (upper:int) (candidate:int)
    (divisor_index:int) <=>
    knuth_prime_numbers_divisible_decrease
      values upper candidate divisor_index /\
    knuth_prime_numbers_reset_state
      values upper (candidate + (&2:int))`;;

let knuth_prime_numbers_advance_branch = new_definition
 `knuth_prime_numbers_advance_branch
    (values:int list) (upper:int) (candidate:int)
    (divisor_index:int) <=>
    let next_index = divisor_index + (&1:int) in
    knuth_prime_numbers_advance_decrease
      values upper candidate divisor_index /\
    (((&1:int) <= next_index /\ next_index < upper) /\
     knuth_prime_numbers_search_state values upper candidate /\
     knuth_prime_numbers_no_divisor_before
       values next_index candidate)`;;

let knuth_prime_numbers_nondivisible_branch = new_definition
 `knuth_prime_numbers_nondivisible_branch
    (values:int list) (upper:int) (candidate:int)
    (divisor_index:int) <=>
    knuth_prime_numbers_index_bound values divisor_index /\
    knuth_prime_numbers_index_bound values divisor_index /\
    (let divisor = knuth_prime_numbers_nth values divisor_index in
     ~(divisor = (&0:int)) /\
     (if knuth_prime_numbers_nth values divisor_index <
         knuth_prime_numbers_cdiv candidate divisor
      then
        knuth_prime_numbers_advance_branch
          values upper candidate divisor_index
      else
        knuth_prime_numbers_candidate_prime
          values upper candidate))`;;

let knuth_prime_numbers_k_branch = new_definition
 `knuth_prime_numbers_k_branch
    (values:int list) (upper:int) (candidate:int)
    (divisor_index:int) <=>
    let divisor = knuth_prime_numbers_nth values divisor_index in
    ~(divisor = (&0:int)) /\
    (if knuth_prime_numbers_cmod candidate divisor = (&0:int)
     then
       knuth_prime_numbers_divisible_branch
         values upper candidate divisor_index
     else
       knuth_prime_numbers_nondivisible_branch
         values upper candidate divisor_index)`;;

let knuth_prime_numbers_k_loop = new_definition
 `knuth_prime_numbers_k_loop
    (values:int list) (upper:int) (candidate:int) <=>
    !divisor_index:int.
      knuth_prime_numbers_k_invariant
        values upper candidate divisor_index
      ==> knuth_prime_numbers_index_bound values divisor_index /\
          knuth_prime_numbers_k_branch
            values upper candidate divisor_index`;;

let knuth_prime_numbers_all_k_loops = new_definition
 `knuth_prime_numbers_all_k_loops
    (reference_values:int list) (upper:int) <=>
    !candidate:int.
    !values:int list.
      LENGTH values = LENGTH reference_values
      ==> knuth_prime_numbers_k_loop values upper candidate`;;

let knuth_prime_numbers_set_preserves_model = new_definition
 `knuth_prime_numbers_set_preserves_model
    (values:int list) (position:int) (value:int) <=>
    LENGTH (knuth_prime_numbers_set values position value) =
      LENGTH values /\
    knuth_prime_numbers_update_law
      (knuth_prime_numbers_set values position value)
      values position value`;;

let knuth_prime_numbers_candidate_insertion = new_definition
 `knuth_prime_numbers_candidate_insertion
    (values:int list) (upper:int) <=>
    !candidate:int.
      knuth_prime_numbers_candidate_prime values upper candidate
      ==> knuth_prime_numbers_index_bound values upper /\
          (knuth_prime_numbers_set_preserves_model
             values upper candidate
           ==> knuth_prime_numbers_search_state
                 (knuth_prime_numbers_set values upper candidate)
                 (upper + (&1:int))
                 (candidate + (&2:int)))`;;

let knuth_prime_numbers_j_step = new_definition
 `knuth_prime_numbers_j_step
    (values:int list) (upper:int) (candidate:int) <=>
    knuth_prime_numbers_all_k_loops values upper /\
    knuth_prime_numbers_reset_state values upper candidate /\
    knuth_prime_numbers_candidate_insertion values upper`;;

let knuth_prime_numbers_all_j_steps = new_definition
 `knuth_prime_numbers_all_j_steps
    (prepared:int list) (requested_length:int) (last_index:int) <=>
    !candidate:int.
    !values:int list.
      LENGTH values = LENGTH prepared
      ==> ((!upper:int.
              knuth_prime_numbers_j_invariant
                values upper candidate last_index
              ==> knuth_prime_numbers_j_step
                    values upper candidate) /\
           (knuth_prime_numbers_search_state
              values (last_index + (&1:int)) candidate
            ==> (&(LENGTH values):int) = requested_length /\
                knuth_prime_numbers_first_primes
                  (knuth_prime_numbers_nth values)
                  requested_length))`;;

let knuth_prime_numbers_main_branch = new_definition
 `knuth_prime_numbers_main_branch
    (prepared:int list) (requested_length:int) (last_index:int) <=>
    knuth_prime_numbers_search_state
      prepared (&2:int) (&5:int) /\
    knuth_prime_numbers_all_j_steps
      prepared requested_length last_index`;;

let knuth_prime_numbers_small_branch = new_definition
 `knuth_prime_numbers_small_branch
    (prepared:int list) (requested_length:int) <=>
    (&(LENGTH prepared):int) = requested_length /\
    knuth_prime_numbers_first_primes
      (knuth_prime_numbers_nth prepared) requested_length`;;

let knuth_prime_numbers_prepared_branches = new_definition
 `knuth_prime_numbers_prepared_branches
    (prepared:int list) (requested_length:int) <=>
    let last_index = requested_length - (&1:int) in
    (((&2:int) <= last_index + (&1:int)
      ==> knuth_prime_numbers_main_branch
            prepared requested_length last_index) /\
     (last_index + (&1:int) < (&2:int)
      ==> knuth_prime_numbers_small_branch
            prepared requested_length))`;;

let knuth_prime_numbers_after_first_set = new_definition
 `knuth_prime_numbers_after_first_set
    (values:int list) (requested_length:int) <=>
    let after_two =
      knuth_prime_numbers_set values (&0:int) (&2:int) in
    let prepared =
      knuth_prime_numbers_set after_two (&1:int) (&3:int) in
    knuth_prime_numbers_index_bound after_two (&1:int) /\
    (knuth_prime_numbers_set_preserves_model
       after_two (&1:int) (&3:int)
     ==> knuth_prime_numbers_prepared_branches
           prepared requested_length)`;;

let knuth_prime_numbers_initialize_list = new_definition
 `knuth_prime_numbers_initialize_list
    (values:int list) (requested_length:int) <=>
    knuth_prime_numbers_index_bound values (&0:int) /\
    (knuth_prime_numbers_set_preserves_model
       values (&0:int) (&2:int)
     ==> knuth_prime_numbers_after_first_set
           values requested_length)`;;

let knuth_prime_numbers_initial_zero_list = new_definition
 `knuth_prime_numbers_initial_zero_list
    (values:int list) (requested_length:int) <=>
    (!i:int.
       (&0:int) <= i /\ i < requested_length
       ==> knuth_prime_numbers_nth values i = (&0:int)) /\
    (&(LENGTH values):int) = requested_length`;;

let statement =
 `(!p:int.
      knuth_prime_numbers_prime p
      ==> ~knuth_prime_numbers_no_prime_in
            p ((&2:int) * p))
  ==>
  !requested_length:int.
    (&2:int) <= requested_length
    ==> (&0:int) <= requested_length /\
        (!values:int list.
           knuth_prime_numbers_initial_zero_list
             values requested_length
           ==> knuth_prime_numbers_initialize_list
                 values requested_length)`;;

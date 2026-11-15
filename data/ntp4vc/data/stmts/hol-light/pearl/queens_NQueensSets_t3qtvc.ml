(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/queens_NQueensSets_t3qtvc: the finite-integer-set verification
  condition for one recursive iteration of the N-queens solution enumerator,
  including its loop invariant and recursive postcondition. This file
  contains no proof.
*)

let nq3_update = new_definition
 `nq3_update (f:A->B) (x:A) (y:B) =
    \z. if z = x then y else f z`;;

let nq3_minimum = new_definition
 `nq3_minimum (s:int->bool) =
    @d:int. d IN s /\ (!x:int. x IN s ==> d <= x)`;;

let nq3_eq_prefix = new_definition
 `nq3_eq_prefix (left:int->A) (right:int->A) (bound:int) <=>
    !i:int.
      (&0:int) <= i /\ i < bound
      ==> left i = right i`;;

let nq3_partial_solution = new_definition
 `nq3_partial_solution
    (n:int) (k:int) (solution:int->int) <=>
    !i:int.
      (&0:int) <= i /\ i < k
      ==>
      ((&0:int) <= solution i /\ solution i < n) /\
      (!j:int.
         (&0:int) <= j /\ j < i
         ==>
         ~(solution i = solution j) /\
         ~(solution i - solution j = i - j) /\
         ~(solution i - solution j = j - i))`;;

let nq3_lt_solution = new_definition
 `nq3_lt_solution
    (n:int) (left:int->int) (right:int->int) <=>
    ?i:int.
      ((&0:int) <= i /\ i < n) /\
      nq3_eq_prefix left right i /\
      left i < right i`;;

let nq3_sorted = new_definition
 `nq3_sorted
    (n:int) (solutions:int->int->int) (lower:int) (upper:int) <=>
    !i j:int.
      lower <= i /\ i < j /\ j < upper
      ==> nq3_lt_solution n (solutions i) (solutions j)`;;

let nq3_available_columns = new_definition
 `nq3_available_columns
    (n:int) (k:int) (available:int->bool) (columns:int->int) <=>
    !i:int.
      i IN available <=>
      ((&0:int) <= i /\ i < n) /\
      (!j:int.
         (&0:int) <= j /\ j < k
         ==> ~(columns j = i))`;;

let nq3_unused_ascending = new_definition
 `nq3_unused_ascending
    (k:int) (diagonals:int->bool) (columns:int->int) <=>
    !i:int.
      (&0:int) <= i
      ==>
      (~(i IN diagonals) <=>
       !j:int.
         (&0:int) <= j /\ j < k
         ==> ~(columns j = i + j - k))`;;

let nq3_unused_descending = new_definition
 `nq3_unused_descending
    (k:int) (diagonals:int->bool) (columns:int->int) <=>
    !i:int.
      (&0:int) <= i
      ==>
      (~(i IN diagonals) <=>
       !j:int.
         (&0:int) <= j /\ j < k
         ==> ~(columns j = i + k - j))`;;

let nq3_call_preconditions = new_definition
 `nq3_call_preconditions
    (n:int) (k:int) (available:int->bool) (next_slot:int)
    (columns:int->int) (ascending:int->bool) (descending:int->bool) <=>
    (&0:int) <= k /\
    k + (&(CARD available):int) = n /\
    (&0:int) <= next_slot /\
    nq3_available_columns n k available columns /\
    nq3_unused_ascending k ascending columns /\
    nq3_unused_descending k descending columns /\
    nq3_partial_solution n k columns`;;

let nq3_insert_condition = new_definition
 `nq3_insert_condition
    (value:int) (base:int->bool) (result:int->bool) <=>
    FINITE result /\
    result = value INSERT base /\
    (if value IN base then
       CARD result = CARD base
     else
       (&(CARD result):int) =
       (&(CARD base):int) + (&1:int))`;;

let nq3_remove_condition = new_definition
 `nq3_remove_condition
    (value:int) (base:int->bool) (result:int->bool) <=>
    FINITE result /\
    result = base DELETE value /\
    (if value IN base then
       (&(CARD result):int) =
       (&(CARD base):int) - (&1:int)
     else
       CARD result = CARD base)`;;

let nq3_successor_condition = new_definition
 `nq3_successor_condition
    (source:int->bool) (result:int->bool) <=>
    FINITE result /\
    (!i:int.
       i IN result <=>
       (&0:int) <= i /\ i + (&1:int) IN source)`;;

let nq3_predecessor_condition = new_definition
 `nq3_predecessor_condition
    (source:int->bool) (result:int->bool) <=>
    FINITE result /\
    (!i:int.
       i IN result <=>
       (&1:int) <= i /\ i - (&1:int) IN source)`;;

let nq3_cardinality_decrease = new_definition
 `nq3_cardinality_decrease
    (before:int->bool) (after:int->bool) <=>
    (&0:int) <= (&(CARD before):int) /\
    (&(CARD after):int) < (&(CARD before):int)`;;

let nq3_loop_invariant = new_definition
 `nq3_loop_invariant
    (n:int) (k:int)
    (available:int->bool) (ascending:int->bool) (descending:int->bool)
    (start:int) (initial_columns:int->int)
    (initial_solutions:int->int->int) (original:int->bool)
    (remaining:int->bool) (finish:int) (columns:int->int)
    (solutions:int->int->int) <=>
    (&0:int) <= finish - start /\
    remaining SUBSET (available DIFF ascending) DIFF descending /\
    nq3_partial_solution n k columns /\
    nq3_sorted n solutions start finish /\
    (!i j:int.
       i IN (original DIFF remaining)
       ==> j IN remaining
       ==> i < j) /\
    (!i:int.
       start <= i /\ i < finish
       ==>
       nq3_partial_solution n n (solutions i) /\
       nq3_eq_prefix columns (solutions i) k /\
       solutions i k IN (original DIFF remaining)) /\
    (!candidate:int->int.
       nq3_partial_solution n n candidate /\
       nq3_eq_prefix columns candidate k /\
       candidate k IN (original DIFF remaining)
       ==>
       candidate k IN original /\
       ~(candidate k IN remaining) /\
       (?i:int.
          (start <= i /\ i < finish) /\
          nq3_eq_prefix candidate (solutions i) n)) /\
    nq3_eq_prefix initial_columns columns k /\
    nq3_eq_prefix initial_solutions solutions start`;;

let nq3_postcondition = new_definition
 `nq3_postcondition
    (n:int) (k:int)
    (initial_columns:int->int) (initial_solutions:int->int->int)
    (start:int) (finish:int) (columns:int->int)
    (solutions:int->int->int) <=>
    (&0:int) <= finish - start /\
    nq3_sorted n solutions start finish /\
    (!candidate:int->int.
       (nq3_partial_solution n n candidate /\
        nq3_eq_prefix columns candidate k) <=>
       ?i:int.
         (start <= i /\ i < finish) /\
         nq3_eq_prefix candidate (solutions i) n) /\
    nq3_eq_prefix initial_columns columns k /\
    nq3_eq_prefix initial_solutions solutions start`;;

let nq3_recursive_iteration = new_definition
 `nq3_recursive_iteration
    (n:int) (k:int)
    (available:int->bool) (ascending:int->bool) (descending:int->bool)
    (start:int) (initial_columns:int->int)
    (initial_solutions:int->int->int) (original:int->bool)
    (remaining:int->bool) (finish:int) (columns:int->int)
    (solutions:int->int->int) (chosen:int) <=>
    !new_descending:int->bool.
      nq3_insert_condition chosen descending new_descending
      ==>
      !shifted_descending:int->bool.
        nq3_successor_condition new_descending shifted_descending
        ==>
        !new_ascending:int->bool.
          nq3_insert_condition chosen ascending new_ascending
          ==>
          !shifted_ascending:int->bool.
            nq3_predecessor_condition new_ascending shifted_ascending
            ==>
            !new_available:int->bool.
              nq3_remove_condition chosen available new_available
              ==>
              (nq3_cardinality_decrease available new_available /\
               nq3_call_preconditions
                 n (k + (&1:int)) new_available finish
                 (nq3_update columns k chosen)
                 shifted_ascending shifted_descending) /\
              (!new_finish:int.
               !new_solutions:int->int->int.
               !new_columns:int->int.
                 nq3_postcondition
                   n (k + (&1:int))
                   (nq3_update columns k chosen) solutions
                   finish new_finish new_columns new_solutions
                 ==>
                 !new_remaining:int->bool.
                   nq3_remove_condition chosen remaining new_remaining
                   ==>
                   nq3_cardinality_decrease remaining new_remaining /\
                   finish - start + (new_finish - finish) =
                     new_finish - start /\
                   k + (&1:int) - (&1:int) = k /\
                   nq3_loop_invariant
                     n (k + (&1:int) - (&1:int))
                     available ascending descending
                     start initial_columns initial_solutions original
                     new_remaining new_finish new_columns new_solutions)`;;

let nq3_loop_result = new_definition
 `nq3_loop_result
    (n:int) (k:int)
    (available:int->bool) (ascending:int->bool) (descending:int->bool)
    (start:int) (initial_columns:int->int)
    (initial_solutions:int->int->int) (original:int->bool)
    (remaining:int->bool) (finish:int) (columns:int->int)
    (solutions:int->int->int) <=>
    if ~(remaining = {}) then
      ~(remaining = {}) /\
      nq3_recursive_iteration
        n k available ascending descending
        start initial_columns initial_solutions original
        remaining finish columns solutions (nq3_minimum remaining)
    else
      nq3_postcondition
        n k initial_columns initial_solutions
        start finish columns solutions`;;

let nq3_all_loop_states = new_definition
 `nq3_all_loop_states
    (n:int) (k:int)
    (available:int->bool) (ascending:int->bool) (descending:int->bool)
    (start:int) (initial_columns:int->int)
    (initial_solutions:int->int->int) (original:int->bool) <=>
    !remaining:int->bool.
    !finish:int.
    !solutions:int->int->int.
    !columns:int->int.
      FINITE remaining /\
      nq3_loop_invariant
        n k available ascending descending
        start initial_columns initial_solutions original
        remaining finish columns solutions
      ==>
      nq3_loop_result
        n k available ascending descending
        start initial_columns initial_solutions original
        remaining finish columns solutions`;;

let statement =
 `!n k:int.
  !available:int->bool.
  !start:int.
  !columns:int->int.
  !ascending descending:int->bool.
  !solutions:int->int->int.
    FINITE available /\
    FINITE ascending /\
    FINITE descending /\
    nq3_call_preconditions
      n k available start columns ascending descending
    ==>
    if ~(available = {}) then
      !first_difference:int->bool.
        FINITE first_difference /\
        first_difference = available DIFF ascending
        ==>
        !original:int->bool.
          FINITE original /\
          original = first_difference DIFF descending
          ==>
          (((&0:int) = start - start /\
            nq3_loop_invariant
              n k available ascending descending
              start columns solutions original
              original start columns solutions) /\
           nq3_all_loop_states
             n k available ascending descending
             start columns solutions original)
    else
      (&1:int) = start + (&1:int) - start /\
      nq3_postcondition
        n k columns solutions
        start (start + (&1:int)) columns
        (nq3_update solutions start columns)`;;

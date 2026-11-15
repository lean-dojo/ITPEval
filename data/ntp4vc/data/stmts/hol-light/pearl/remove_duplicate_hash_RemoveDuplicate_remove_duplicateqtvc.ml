(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/remove_duplicate_hash_RemoveDuplicate_remove_duplicateqtvc: the
  duplicate-removal verification condition for finite-set accumulation,
  initialized result storage, loop invariants, and duplicate-free output.
  This file contains no proof.
*)

let rdh_int_index = new_definition
 `rdh_int_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let rdh_nth = new_definition
 `rdh_nth (a:A list) (i:int) =
    if rdh_int_index i < LENGTH a
    then EL (rdh_int_index i) a
    else ARB`;;

let rdh_update_nat =
  new_recursive_definition list_RECURSION
   `(!n:num. !x:A. rdh_update_nat [] n x = []) /\
    (!h:A. !t:A list. !n:num. !x:A.
       rdh_update_nat (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (rdh_update_nat t (PRE n) x))`;;

let rdh_update = new_definition
 `rdh_update (a:A list) (i:int) (x:A) =
    rdh_update_nat a (rdh_int_index i) x`;;

let rdh_appears = new_definition
 `rdh_appears (x:A) (a:A list) (s:int) <=>
    ?i:int.
      ((&0:int) <= i /\ i < s) /\
      rdh_nth a i = x`;;

let rdh_nodup = new_definition
 `rdh_nodup (a:A list) (s:int) <=>
    !i:int.
      (&0:int) <= i /\ i < s
      ==> ~rdh_appears (rdh_nth a i) a i`;;

let rdh_appears_equals_set = new_definition
 `rdh_appears_equals_set
    (to_fset:B->A->bool) (a:A list) (size:int) (set:B) <=>
    !x:A. rdh_appears x a size <=> x IN to_fset set`;;

let rdh_set_equals_appears = new_definition
 `rdh_set_equals_appears
    (to_fset:B->A->bool) (set:B) (a:A list) (size:int) <=>
    !x:A. x IN to_fset set <=> rdh_appears x a size`;;

let rdh_appears_equals_appears = new_definition
 `rdh_appears_equals_appears
    (a:A list) (a_size:int) (r:A list) (r_size:int) <=>
    !x:A. rdh_appears x a a_size <=> rdh_appears x r r_size`;;

let rdh_add_premise = new_definition
 `rdh_add_premise
    (to_fset:B->A->bool) (new_set:B) (value:A) (old_set:B) <=>
    to_fset new_set = value INSERT to_fset old_set /\
    (if value IN to_fset old_set
     then CARD (to_fset new_set) = CARD (to_fset old_set)
     else (&(CARD (to_fset new_set)):int) =
          (&(CARD (to_fset old_set)):int) + (&1:int))`;;

let rdh_second_invariant = new_definition
 `rdh_second_invariant
    (to_fset:B->A->bool)
    (a:A list) (outer_set:B) (r:A list) (current_set:B)
    (i:int) (j:int) (o3:int) <=>
    ((&0:int) <= i /\ i <= o3) /\
    rdh_appears_equals_set to_fset a i current_set /\
    rdh_set_equals_appears to_fset current_set r j /\
    rdh_nodup r j /\
    ((&0:int) <= j /\
     j = (&(CARD (to_fset current_set)):int) /\
     CARD (to_fset current_set) <= LENGTH r) /\
    to_fset current_set SUBSET to_fset outer_set`;;

let rdh_second_updated_invariant = new_definition
 `rdh_second_updated_invariant
    (to_fset:B->A->bool)
    (a:A list) (outer_set:B) (updated_r:A list) (updated_set:B)
    (i:int) (j:int) <=>
    rdh_appears_equals_set to_fset a (i + (&1:int)) updated_set /\
    rdh_set_equals_appears
      to_fset updated_set updated_r (j + (&1:int)) /\
    rdh_nodup updated_r (j + (&1:int)) /\
    ((&0:int) <= j + (&1:int) /\
     j + (&1:int) = (&(CARD (to_fset updated_set)):int) /\
     CARD (to_fset updated_set) <= LENGTH updated_r) /\
    to_fset updated_set SUBSET to_fset outer_set`;;

let rdh_inserted_list_conclusion = new_definition
 `rdh_inserted_list_conclusion
    (to_fset:B->A->bool)
    (a:A list) (outer_set:B) (r:A list) (new_set:B)
    (i:int) (j:int) <=>
    let value = rdh_nth a i in
    let updated_r = rdh_update r j value in
    ((&0:int) <= j /\ j < (&(LENGTH r):int)) /\
    (LENGTH updated_r = LENGTH r
     ==>
     (\k:int. rdh_nth updated_r k) =
       (\k:int. if k = j then value else rdh_nth r k)
     ==>
     rdh_second_updated_invariant
       to_fset a outer_set updated_r new_set i j)`;;

let rdh_after_set_insert = new_definition
 `rdh_after_set_insert
    (to_fset:B->A->bool)
    (a:A list) (outer_set:B) (r:A list) (current_set:B)
    (i:int) (j:int) <=>
    !new_set:B.
      rdh_add_premise to_fset new_set (rdh_nth a i) current_set
      ==>
      ((&0:int) <= i /\ i < (&(LENGTH a):int)) /\
      rdh_inserted_list_conclusion
        to_fset a outer_set r new_set i j`;;

let rdh_second_loop_step = new_definition
 `rdh_second_loop_step
    (to_fset:B->A->bool)
    (a:A list) (outer_set:B) (r:A list) (current_set:B)
    (i:int) (j:int) <=>
    ((&0:int) <= i /\ i < (&(LENGTH a):int)) /\
    (if ~(rdh_nth a i IN to_fset current_set)
     then
       ((&0:int) <= i /\ i < (&(LENGTH a):int)) /\
       rdh_after_set_insert
         to_fset a outer_set r current_set i j
     else
       rdh_appears_equals_set
         to_fset a (i + (&1:int)) current_set /\
       rdh_set_equals_appears to_fset current_set r j /\
       rdh_nodup r j /\
       ((&0:int) <= j /\
        j = (&(CARD (to_fset current_set)):int) /\
        CARD (to_fset current_set) <= LENGTH r) /\
       to_fset current_set SUBSET to_fset outer_set)`;;

let rdh_second_loop_case = new_definition
 `rdh_second_loop_case
    (to_fset:B->A->bool)
    (a:A list) (outer_set:B) (r:A list) (current_set:B)
    (i:int) (j:int) (o3:int) <=>
    rdh_second_invariant
      to_fset a outer_set r current_set i j o3
    ==>
    rdh_second_loop_step
      to_fset a outer_set r current_set i j`;;

let rdh_all_second_loop_cases = new_definition
 `rdh_all_second_loop_cases
    (to_fset:B->A->bool)
    (a:A list) (outer_set:B) (r:A list) (current_set:B)
    (j:int) (o3:int) <=>
    !i:int.
      rdh_second_loop_case
        to_fset a outer_set r current_set i j o3`;;

let rdh_second_final_invariant = new_definition
 `rdh_second_final_invariant
    (to_fset:B->A->bool)
    (a:A list) (outer_set:B) (r:A list) (current_set:B)
    (j:int) (o3:int) <=>
    rdh_appears_equals_set
      to_fset a (o3 + (&1:int)) current_set /\
    rdh_set_equals_appears to_fset current_set r j /\
    rdh_nodup r j /\
    ((&0:int) <= j /\
     j = (&(CARD (to_fset current_set)):int) /\
     CARD (to_fset current_set) <= LENGTH r) /\
    to_fset current_set SUBSET to_fset outer_set`;;

let rdh_output_postcondition = new_definition
 `rdh_output_postcondition (a:A list) (r:A list) <=>
    rdh_nodup r (&(LENGTH r):int) /\
    rdh_appears_equals_appears
      a (&(LENGTH a):int) r (&(LENGTH r):int)`;;

let rdh_second_state_conclusion = new_definition
 `rdh_second_state_conclusion
    (to_fset:B->A->bool)
    (a:A list) (outer_set:B) (r:A list) (current_set:B)
    (j:int) (o3:int) <=>
    rdh_all_second_loop_cases
      to_fset a outer_set r current_set j o3 /\
    (rdh_second_final_invariant
       to_fset a outer_set r current_set j o3
     ==>
     rdh_output_postcondition a r)`;;

let rdh_all_second_loop_states = new_definition
 `rdh_all_second_loop_states
    (to_fset:B->A->bool)
    (a:A list) (outer_set:B) (initial_r:A list) (o3:int) <=>
    !j:int. !r:A list. !current_set:B.
      LENGTH r = LENGTH initial_r
      ==>
      rdh_second_state_conclusion
        to_fset a outer_set r current_set j o3`;;

let rdh_second_loop_initial = new_definition
 `rdh_second_loop_initial
    (to_fset:B->A->bool)
    (a:A list) (outer_set:B) (initial_r:A list) (empty_set:B) <=>
    rdh_appears_equals_set to_fset a (&0:int) empty_set /\
    rdh_set_equals_appears to_fset empty_set initial_r (&0:int) /\
    rdh_nodup initial_r (&0:int) /\
    ((&0:int) <= (&0:int) /\
     (&0:int) = (&(CARD (to_fset empty_set)):int) /\
     CARD (to_fset empty_set) <= LENGTH initial_r) /\
    to_fset empty_set SUBSET to_fset outer_set`;;

let rdh_second_loop_vc = new_definition
 `rdh_second_loop_vc
    (to_fset:B->A->bool)
    (a:A list) (outer_set:B) (initial_r:A list) (empty_set:B) <=>
    let o3 = (&(LENGTH a):int) - (&1:int) in
    (((&0:int) <= o3 + (&1:int)
      ==>
      rdh_second_loop_initial
        to_fset a outer_set initial_r empty_set /\
      rdh_all_second_loop_states
        to_fset a outer_set initial_r o3) /\
     (o3 + (&1:int) < (&0:int)
      ==>
      rdh_output_postcondition a initial_r))`;;

let rdh_all_empty_set_continuations = new_definition
 `rdh_all_empty_set_continuations
    (to_fset:B->A->bool)
    (a:A list) (outer_set:B) (initial_r:A list) <=>
    !empty_set:B.
      to_fset empty_set = {}
      ==>
      rdh_second_loop_vc
        to_fset a outer_set initial_r empty_set`;;

let rdh_initialized_list = new_definition
 `rdh_initialized_list (a:A list) (r:A list) (size:int) <=>
    !i:int.
      (&0:int) <= i /\ i < size
      ==> rdh_nth r i = rdh_nth a (&0:int)`;;

let rdh_all_result_lists = new_definition
 `rdh_all_result_lists
    (to_fset:B->A->bool)
    (a:A list) (outer_set:B) (size:int) <=>
    !r:A list.
      rdh_initialized_list a r size /\
      (&(LENGTH r):int) = size
      ==>
      rdh_all_empty_set_continuations
        to_fset a outer_set r`;;

let rdh_second_phase = new_definition
 `rdh_second_phase
    (to_fset:B->A->bool) (a:A list) (outer_set:B) <=>
    ((&0:int) <= (&0:int) /\ (&0:int) < (&(LENGTH a):int)) /\
    (let size = (&(CARD (to_fset outer_set)):int) in
     (&0:int) <= size /\
     rdh_all_result_lists to_fset a outer_set size)`;;

let rdh_first_invariant = new_definition
 `rdh_first_invariant
    (to_fset:B->A->bool)
    (a:A list) (current_set:B) (i:int) (o1:int) <=>
    ((&0:int) <= i /\ i <= o1) /\
    rdh_appears_equals_set to_fset a i current_set`;;

let rdh_first_after_insert = new_definition
 `rdh_first_after_insert
    (to_fset:B->A->bool)
    (a:A list) (current_set:B) (i:int) <=>
    !new_set:B.
      rdh_add_premise to_fset new_set (rdh_nth a i) current_set
      ==>
      rdh_appears_equals_set
        to_fset a (i + (&1:int)) new_set`;;

let rdh_first_loop_case = new_definition
 `rdh_first_loop_case
    (to_fset:B->A->bool)
    (a:A list) (current_set:B) (i:int) (o1:int) <=>
    rdh_first_invariant to_fset a current_set i o1
    ==>
    ((&0:int) <= i /\ i < (&(LENGTH a):int)) /\
    rdh_first_after_insert to_fset a current_set i`;;

let rdh_all_first_loop_cases = new_definition
 `rdh_all_first_loop_cases
    (to_fset:B->A->bool)
    (a:A list) (current_set:B) (o1:int) <=>
    !i:int.
      rdh_first_loop_case to_fset a current_set i o1`;;

let rdh_first_loop_set_conclusion = new_definition
 `rdh_first_loop_set_conclusion
    (to_fset:B->A->bool)
    (a:A list) (current_set:B) (o1:int) <=>
    rdh_all_first_loop_cases to_fset a current_set o1 /\
    (rdh_appears_equals_set
       to_fset a (o1 + (&1:int)) current_set
     ==>
     rdh_second_phase to_fset a current_set)`;;

let rdh_all_first_loop_sets = new_definition
 `rdh_all_first_loop_sets
    (to_fset:B->A->bool) (a:A list) (o1:int) <=>
    !current_set:B.
      rdh_first_loop_set_conclusion
        to_fset a current_set o1`;;

let rdh_main_vc = new_definition
 `rdh_main_vc
    (to_fset:B->A->bool) (a:A list) (initial_set:B) <=>
    let o1 = (&(LENGTH a):int) - (&1:int) in
    (((&0:int) <= o1 + (&1:int)
      ==>
      rdh_appears_equals_set
        to_fset a (&0:int) initial_set /\
      rdh_all_first_loop_sets to_fset a o1) /\
     (o1 + (&1:int) < (&0:int)
      ==>
      rdh_second_phase to_fset a initial_set))`;;

let statement =
 `!to_fset:B->A->bool.
    (!set:B. FINITE (to_fset set))
    ==>
    !a:A list. !initial_set:B.
      (&1:int) <= (&(LENGTH a):int)
      ==>
      to_fset initial_set = {}
      ==>
      (&(CARD (to_fset initial_set)):int) = (&0:int)
      ==>
      rdh_main_vc to_fset a initial_set`;;

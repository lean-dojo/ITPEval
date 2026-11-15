(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/remove_duplicate_hash_RemoveDuplicate_remove_duplicateqtvc: the
  duplicate-removal verification condition for finite-set accumulation,
  initialized result storage, loop invariants, and duplicate-free output.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory pred_setTheory;

val remove_duplicate_hash_RemoveDuplicate_remove_duplicate_vc =
  ``let rdh_int_index =
      \i : int. if i < 0 then 0 else Num i
    in
    let rdh_nth =
      \a : 'a list. \i : int.
        if rdh_int_index i < LENGTH a
        then EL (rdh_int_index i) a
        else ARB
    in
    let rdh_update =
      \a : 'a list. \i : int. \x : 'a.
        LUPDATE x (rdh_int_index i) a
    in
    let rdh_appears =
      \x : 'a. \a : 'a list. \s : int.
        ?i : int.
          (0 <= i /\ i < s) /\
          rdh_nth a i = x
    in
    let rdh_nodup =
      \a : 'a list. \s : int.
        !i : int.
          0 <= i /\ i < s ==>
          ~rdh_appears (rdh_nth a i) a i
    in
    let rdh_appears_equals_set =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \size : int. \set : 'b.
        !x : 'a.
          (rdh_appears x a size <=> x IN to_fset set)
    in
    let rdh_set_equals_appears =
      \to_fset : 'b -> 'a set.
      \set : 'b. \a : 'a list. \size : int.
        !x : 'a.
          (x IN to_fset set <=> rdh_appears x a size)
    in
    let rdh_appears_equals_appears =
      \a : 'a list. \a_size : int.
      \r : 'a list. \r_size : int.
        !x : 'a.
          (rdh_appears x a a_size <=>
           rdh_appears x r r_size)
    in
    let rdh_add_premise =
      \to_fset : 'b -> 'a set.
      \new_set : 'b. \value : 'a. \old_set : 'b.
        to_fset new_set = value INSERT to_fset old_set /\
        (if value IN to_fset old_set
         then CARD (to_fset new_set) = CARD (to_fset old_set)
         else &(CARD (to_fset new_set)) =
              &(CARD (to_fset old_set)) + 1)
    in
    let rdh_second_invariant =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \outer_set : 'b.
      \r : 'a list. \current_set : 'b.
      \i : int. \j : int. \o3 : int.
        (0 <= i /\ i <= o3) /\
        rdh_appears_equals_set to_fset a i current_set /\
        rdh_set_equals_appears to_fset current_set r j /\
        rdh_nodup r j /\
        (0 <= j /\
         j = &(CARD (to_fset current_set)) /\
         CARD (to_fset current_set) <= LENGTH r) /\
        to_fset current_set SUBSET to_fset outer_set
    in
    let rdh_second_updated_invariant =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \outer_set : 'b.
      \updated_r : 'a list. \updated_set : 'b.
      \i : int. \j : int.
        rdh_appears_equals_set
          to_fset a (i + 1) updated_set /\
        rdh_set_equals_appears
          to_fset updated_set updated_r (j + 1) /\
        rdh_nodup updated_r (j + 1) /\
        (0 <= j + 1 /\
         j + 1 = &(CARD (to_fset updated_set)) /\
         CARD (to_fset updated_set) <= LENGTH updated_r) /\
        to_fset updated_set SUBSET to_fset outer_set
    in
    let rdh_inserted_list_conclusion =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \outer_set : 'b.
      \r : 'a list. \new_set : 'b.
      \i : int. \j : int.
        let value = rdh_nth a i in
        let updated_r = rdh_update r j value in
          (0 <= j /\ j < &(LENGTH r)) /\
          (LENGTH updated_r = LENGTH r ==>
           (\k : int. rdh_nth updated_r k) =
             (\k : int.
                if k = j then value else rdh_nth r k) ==>
           rdh_second_updated_invariant
             to_fset a outer_set updated_r new_set i j)
    in
    let rdh_after_set_insert =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \outer_set : 'b.
      \r : 'a list. \current_set : 'b.
      \i : int. \j : int.
        !new_set : 'b.
          rdh_add_premise
            to_fset new_set (rdh_nth a i) current_set ==>
          (0 <= i /\ i < &(LENGTH a)) /\
          rdh_inserted_list_conclusion
            to_fset a outer_set r new_set i j
    in
    let rdh_second_loop_step =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \outer_set : 'b.
      \r : 'a list. \current_set : 'b.
      \i : int. \j : int.
        (0 <= i /\ i < &(LENGTH a)) /\
        (if ~(rdh_nth a i IN to_fset current_set)
         then
           (0 <= i /\ i < &(LENGTH a)) /\
           rdh_after_set_insert
             to_fset a outer_set r current_set i j
         else
           rdh_appears_equals_set
             to_fset a (i + 1) current_set /\
           rdh_set_equals_appears
             to_fset current_set r j /\
           rdh_nodup r j /\
           (0 <= j /\
            j = &(CARD (to_fset current_set)) /\
            CARD (to_fset current_set) <= LENGTH r) /\
           to_fset current_set SUBSET to_fset outer_set)
    in
    let rdh_second_loop_case =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \outer_set : 'b.
      \r : 'a list. \current_set : 'b.
      \i : int. \j : int. \o3 : int.
        rdh_second_invariant
          to_fset a outer_set r current_set i j o3 ==>
        rdh_second_loop_step
          to_fset a outer_set r current_set i j
    in
    let rdh_all_second_loop_cases =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \outer_set : 'b.
      \r : 'a list. \current_set : 'b.
      \j : int. \o3 : int.
        !i : int.
          rdh_second_loop_case
            to_fset a outer_set r current_set i j o3
    in
    let rdh_second_final_invariant =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \outer_set : 'b.
      \r : 'a list. \current_set : 'b.
      \j : int. \o3 : int.
        rdh_appears_equals_set
          to_fset a (o3 + 1) current_set /\
        rdh_set_equals_appears to_fset current_set r j /\
        rdh_nodup r j /\
        (0 <= j /\
         j = &(CARD (to_fset current_set)) /\
         CARD (to_fset current_set) <= LENGTH r) /\
        to_fset current_set SUBSET to_fset outer_set
    in
    let rdh_output_postcondition =
      \a : 'a list. \r : 'a list.
        rdh_nodup r (&(LENGTH r)) /\
        rdh_appears_equals_appears
          a (&(LENGTH a)) r (&(LENGTH r))
    in
    let rdh_second_state_conclusion =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \outer_set : 'b.
      \r : 'a list. \current_set : 'b.
      \j : int. \o3 : int.
        rdh_all_second_loop_cases
          to_fset a outer_set r current_set j o3 /\
        (rdh_second_final_invariant
           to_fset a outer_set r current_set j o3 ==>
         rdh_output_postcondition a r)
    in
    let rdh_all_second_loop_states =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \outer_set : 'b.
      \initial_r : 'a list. \o3 : int.
        !j : int. !r : 'a list. !current_set : 'b.
          LENGTH r = LENGTH initial_r ==>
          rdh_second_state_conclusion
            to_fset a outer_set r current_set j o3
    in
    let rdh_second_loop_initial =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \outer_set : 'b.
      \initial_r : 'a list. \empty_set : 'b.
        rdh_appears_equals_set
          to_fset a 0 empty_set /\
        rdh_set_equals_appears
          to_fset empty_set initial_r 0 /\
        rdh_nodup initial_r 0 /\
        (0 <= (0 : int) /\
         (0 : int) = &(CARD (to_fset empty_set)) /\
         CARD (to_fset empty_set) <= LENGTH initial_r) /\
        to_fset empty_set SUBSET to_fset outer_set
    in
    let rdh_second_loop_vc =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \outer_set : 'b.
      \initial_r : 'a list. \empty_set : 'b.
        let o3 = &(LENGTH a) - 1 in
          (0 <= o3 + 1 ==>
             rdh_second_loop_initial
               to_fset a outer_set initial_r empty_set /\
             rdh_all_second_loop_states
               to_fset a outer_set initial_r o3) /\
          (o3 + 1 < 0 ==>
             rdh_output_postcondition a initial_r)
    in
    let rdh_all_empty_set_continuations =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \outer_set : 'b.
      \initial_r : 'a list.
        !empty_set : 'b.
          to_fset empty_set = {} ==>
          rdh_second_loop_vc
            to_fset a outer_set initial_r empty_set
    in
    let rdh_initialized_list =
      \a : 'a list. \r : 'a list. \size : int.
        !i : int.
          0 <= i /\ i < size ==>
          rdh_nth r i = rdh_nth a 0
    in
    let rdh_all_result_lists =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \outer_set : 'b. \size : int.
        !r : 'a list.
          rdh_initialized_list a r size /\
          &(LENGTH r) = size ==>
          rdh_all_empty_set_continuations
            to_fset a outer_set r
    in
    let rdh_second_phase =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \outer_set : 'b.
        (0 <= (0 : int) /\ (0 : int) < &(LENGTH a)) /\
        (let size = &(CARD (to_fset outer_set)) in
           0 <= size /\
           rdh_all_result_lists
             to_fset a outer_set size)
    in
    let rdh_first_invariant =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \current_set : 'b.
      \i : int. \o1 : int.
        (0 <= i /\ i <= o1) /\
        rdh_appears_equals_set to_fset a i current_set
    in
    let rdh_first_after_insert =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \current_set : 'b. \i : int.
        !new_set : 'b.
          rdh_add_premise
            to_fset new_set (rdh_nth a i) current_set ==>
          rdh_appears_equals_set
            to_fset a (i + 1) new_set
    in
    let rdh_first_loop_case =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \current_set : 'b.
      \i : int. \o1 : int.
        rdh_first_invariant
          to_fset a current_set i o1 ==>
        (0 <= i /\ i < &(LENGTH a)) /\
        rdh_first_after_insert
          to_fset a current_set i
    in
    let rdh_all_first_loop_cases =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \current_set : 'b. \o1 : int.
        !i : int.
          rdh_first_loop_case
            to_fset a current_set i o1
    in
    let rdh_first_loop_set_conclusion =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \current_set : 'b. \o1 : int.
        rdh_all_first_loop_cases
          to_fset a current_set o1 /\
        (rdh_appears_equals_set
           to_fset a (o1 + 1) current_set ==>
         rdh_second_phase to_fset a current_set)
    in
    let rdh_all_first_loop_sets =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \o1 : int.
        !current_set : 'b.
          rdh_first_loop_set_conclusion
            to_fset a current_set o1
    in
    let rdh_main_vc =
      \to_fset : 'b -> 'a set.
      \a : 'a list. \initial_set : 'b.
        let o1 = &(LENGTH a) - 1 in
          (0 <= o1 + 1 ==>
             rdh_appears_equals_set
               to_fset a 0 initial_set /\
             rdh_all_first_loop_sets
               to_fset a o1) /\
          (o1 + 1 < 0 ==>
             rdh_second_phase
               to_fset a initial_set)
    in
      !to_fset : 'b -> 'a set.
        (!set : 'b. FINITE (to_fset set)) ==>
        !a : 'a list. !initial_set : 'b.
          (1 : int) <= &(LENGTH a) ==>
          to_fset initial_set = {} ==>
          &(CARD (to_fset initial_set)) = (0 : int) ==>
          rdh_main_vc to_fset a initial_set``;

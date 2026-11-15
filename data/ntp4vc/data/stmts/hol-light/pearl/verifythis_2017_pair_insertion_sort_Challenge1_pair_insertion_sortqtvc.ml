(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2017_pair_insertion_sort_Challenge1_pair_insertion_sortqtvc:
  the pair-insertion-sort verification condition for integer arrays, including
  the outer sorted-prefix invariant, two insertion loops, array updates,
  permutation preservation, termination measures, and final sortedness.
  This file contains no proof.
*)

ignore (new_definition
 `pair_insert_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`);;

ignore (new_definition
 `pair_insert_nth (a:int list) (i:int) =
    if i < (&0:int) then (&0:int)
    else if pair_insert_to_num i < LENGTH a
    then EL (pair_insert_to_num i) a
    else (&0:int)`);;

ignore (new_recursive_definition list_RECURSION
   `(!n:num. !x:int.
       pair_insert_update [] n x = []) /\
    (!h:int. !t:int list. !n:num. !x:int.
       pair_insert_update (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (pair_insert_update t (PRE n) x))`);;

ignore (new_definition
 `pair_insert_permut (a:int list) (b:int list) <=>
    LENGTH a = LENGTH b /\
    (!v:int.
       CARD {k:num | k < LENGTH a /\ EL k a = v} =
       CARD {k:num | k < LENGTH b /\ EL k b = v})`);;

ignore (new_definition
 `pair_insert_sorted_upto (a:int list) (u:int) <=>
    !k l:int.
      (&0:int) <= k /\ k <= l /\ l < u
      ==> pair_insert_nth a k <= pair_insert_nth a l`);;

ignore (new_definition
 `pair_insert_sorted_closed (a:int list) (j:int) <=>
    !k l:int.
      (&0:int) <= k /\ k <= l /\ l <= j
      ==> pair_insert_nth a k <= pair_insert_nth a l`);;

ignore (new_definition
 `pair_insert_first_invariant
    (original:int list) (i:int) (x:int) (y:int)
    (j:int) (current:int list) <=>
    ((&0:int) - (&1:int) <= j /\ j < i) /\
    pair_insert_sorted_closed current j /\
    (!k l:int.
       (&0:int) <= k /\ k <= j
       ==> j + (&2:int) < l /\ l < i + (&2:int)
       ==> pair_insert_nth current k <= pair_insert_nth current l) /\
    (!k l:int.
       j + (&2:int) < k /\ k <= l /\ l < i + (&2:int)
       ==> pair_insert_nth current k <= pair_insert_nth current l) /\
    (!l:int.
       j + (&2:int) < l /\ l < i + (&2:int)
       ==> x < pair_insert_nth current l) /\
    pair_insert_permut
      original
      (pair_insert_update
        (pair_insert_update
          current (pair_insert_to_num (j + (&1:int))) y)
        (pair_insert_to_num (j + (&2:int))) x)`);;

ignore (new_definition
 `pair_insert_second_invariant
    (original:int list) (i:int) (y:int)
    (j:int) (current:int list) <=>
    ((&0:int) - (&1:int) <= j /\ j < i) /\
    pair_insert_sorted_closed current j /\
    (!k l:int.
       (&0:int) <= k /\ k <= j
       ==> j + (&1:int) < l /\ l < i + (&2:int)
       ==> pair_insert_nth current k <= pair_insert_nth current l) /\
    (!k l:int.
       j + (&1:int) < k /\ k <= l /\ l < i + (&2:int)
       ==> pair_insert_nth current k <= pair_insert_nth current l) /\
    (!l:int.
       j + (&1:int) < l /\ l < i + (&2:int)
       ==> y <= pair_insert_nth current l) /\
    pair_insert_permut
      original
      (pair_insert_update
        current (pair_insert_to_num (j + (&1:int))) y)`);;

ignore (new_definition
 `pair_insert_outer_next
    (original:int list) (base:int list) (i:int) (current:int list) <=>
    ((&0:int) <= (&(LENGTH base):int) - i /\
     (&(LENGTH current):int) - (i + (&2:int)) <
       (&(LENGTH base):int) - i) /\
    ((&0:int) <= i + (&2:int) /\
     i + (&2:int) <= (&(LENGTH current):int)) /\
    pair_insert_sorted_upto current (i + (&2:int)) /\
    pair_insert_permut original current`);;

ignore (new_definition
 `pair_insert_second_step
    (original:int list) (base:int list) (i:int) (y:int)
    (j:int) (current:int list) <=>
    ((&0:int) <= j
     ==> (&0:int) <= j /\ j < (&(LENGTH current):int)) /\
    (!test:bool.
       (if (&0:int) <= j
        then test =
             (if y < pair_insert_nth current j then T else F)
        else test = F)
       ==>
       if test = T then
         ((&0:int) <= j /\ j < (&(LENGTH current):int)) /\
         (let shifted_value = pair_insert_nth current j in
          let position = j + (&1:int) in
          ((&0:int) <= position /\
           position < (&(LENGTH current):int)) /\
          (let shifted =
             pair_insert_update
               current (pair_insert_to_num position) shifted_value in
           LENGTH shifted = LENGTH current
           ==>
           (!r:int.
              pair_insert_nth shifted r =
              if r = position
              then shifted_value
              else pair_insert_nth current r)
           ==>
           ((&0:int) <= j /\ j - (&1:int) < j) /\
           pair_insert_second_invariant
             original i y (j - (&1:int)) shifted))
       else
         let position = j + (&1:int) in
         ((&0:int) <= position /\
          position < (&(LENGTH current):int)) /\
         (let placed =
            pair_insert_update
              current (pair_insert_to_num position) y in
          LENGTH placed = LENGTH current
          ==>
          (!r:int.
             pair_insert_nth placed r =
             if r = position then y else pair_insert_nth current r)
          ==>
          pair_insert_outer_next original base i placed))`);;

ignore (new_definition
 `pair_insert_second_phase
    (original:int list) (base:int list) (i:int) (y:int)
    (j:int) (current:int list) <=>
    pair_insert_second_invariant original i y j current /\
    (!j1:int. !next:int list.
       LENGTH next = LENGTH current
       ==>
       pair_insert_second_invariant original i y j1 next
       ==>
       pair_insert_second_step original base i y j1 next)`);;

ignore (new_definition
 `pair_insert_first_step
    (original:int list) (base:int list) (i:int) (x:int) (y:int)
    (j:int) (current:int list) <=>
    ((&0:int) <= j
     ==> (&0:int) <= j /\ j < (&(LENGTH current):int)) /\
    (!test:bool.
       (if (&0:int) <= j
        then test =
             (if x < pair_insert_nth current j then T else F)
        else test = F)
       ==>
       if test = T then
         ((&0:int) <= j /\ j < (&(LENGTH current):int)) /\
         (let shifted_value = pair_insert_nth current j in
          let position = j + (&2:int) in
          ((&0:int) <= position /\
           position < (&(LENGTH current):int)) /\
          (let shifted =
             pair_insert_update
               current (pair_insert_to_num position) shifted_value in
           LENGTH shifted = LENGTH current
           ==>
           (!r:int.
              pair_insert_nth shifted r =
              if r = position
              then shifted_value
              else pair_insert_nth current r)
           ==>
           ((&0:int) <= j /\ j - (&1:int) < j) /\
           pair_insert_first_invariant
             original i x y (j - (&1:int)) shifted))
       else
         let position = j + (&2:int) in
         ((&0:int) <= position /\
          position < (&(LENGTH current):int)) /\
         (let placed =
            pair_insert_update
              current (pair_insert_to_num position) x in
          LENGTH placed = LENGTH current
          ==>
          (!r:int.
             pair_insert_nth placed r =
             if r = position then x else pair_insert_nth current r)
          ==>
          pair_insert_second_phase
            original base i y j placed))`);;

ignore (new_definition
 `pair_insert_first_phase
    (original:int list) (base:int list) (i:int) (x:int) (y:int)
    (j:int) (current:int list) <=>
    pair_insert_first_invariant original i x y j current /\
    (!j1:int. !next:int list.
       LENGTH next = LENGTH current
       ==>
       pair_insert_first_invariant original i x y j1 next
       ==>
       pair_insert_first_step original base i x y j1 next)`);;

ignore (new_definition
 `pair_insert_pair_case
    (original:int list) (base:int list) (i:int) <=>
    ((&0:int) <= i /\ i < (&(LENGTH base):int)) /\
    (let first = pair_insert_nth base i in
     let next_index = i + (&1:int) in
     ((&0:int) <= next_index /\
      next_index < (&(LENGTH base):int)) /\
     (let second = pair_insert_nth base next_index in
      if first < second then
        pair_insert_first_phase
          original base i second first (i - (&1:int)) base
      else
        pair_insert_first_phase
          original base i first second (i - (&1:int)) base))`);;

ignore (new_definition
 `pair_insert_single_invariant
    (original:int list) (i:int) (y:int)
    (j:int) (current:int list) <=>
    ((&0:int) - (&1:int) <= j /\ j < i) /\
    pair_insert_sorted_closed current j /\
    (!k l:int.
       (&0:int) <= k /\ k <= j
       ==> j + (&1:int) < l /\ l < (&(LENGTH current):int)
       ==> pair_insert_nth current k <= pair_insert_nth current l) /\
    (!k l:int.
       j + (&1:int) < k /\ k <= l /\ l < (&(LENGTH current):int)
       ==> pair_insert_nth current k <= pair_insert_nth current l) /\
    (!l:int.
       j + (&1:int) < l /\ l < (&(LENGTH current):int)
       ==> y < pair_insert_nth current l) /\
    pair_insert_permut
      original
      (pair_insert_update
        current (pair_insert_to_num (j + (&1:int))) y)`);;

ignore (new_definition
 `pair_insert_single_step
    (original:int list) (i:int) (y:int)
    (j:int) (current:int list) <=>
    ((&0:int) <= j
     ==> (&0:int) <= j /\ j < (&(LENGTH current):int)) /\
    (!test:bool.
       (if (&0:int) <= j
        then test =
             (if y < pair_insert_nth current j then T else F)
        else test = F)
       ==>
       if test = T then
         ((&0:int) <= j /\ j < (&(LENGTH current):int)) /\
         (let shifted_value = pair_insert_nth current j in
          let position = j + (&1:int) in
          ((&0:int) <= position /\
           position < (&(LENGTH current):int)) /\
          (let shifted =
             pair_insert_update
               current (pair_insert_to_num position) shifted_value in
           LENGTH shifted = LENGTH current
           ==>
           (!r:int.
              pair_insert_nth shifted r =
              if r = position
              then shifted_value
              else pair_insert_nth current r)
           ==>
           ((&0:int) <= j /\ j - (&1:int) < j) /\
           pair_insert_single_invariant
             original i y (j - (&1:int)) shifted))
       else
         let position = j + (&1:int) in
         ((&0:int) <= position /\
          position < (&(LENGTH current):int)) /\
         (let placed =
            pair_insert_update
              current (pair_insert_to_num position) y in
          LENGTH placed = LENGTH current
          ==>
          (!r:int.
             pair_insert_nth placed r =
             if r = position then y else pair_insert_nth current r)
          ==>
          pair_insert_sorted_upto placed (&(LENGTH placed):int) /\
          pair_insert_permut original placed))`);;

ignore (new_definition
 `pair_insert_single_phase
    (original:int list) (i:int) (y:int)
    (j:int) (current:int list) <=>
    pair_insert_single_invariant original i y j current /\
    (!j1:int. !next:int list.
       LENGTH next = LENGTH current
       ==>
       pair_insert_single_invariant original i y j1 next
       ==>
       pair_insert_single_step original i y j1 next)`);;

ignore (new_definition
 `pair_insert_single_case
    (original:int list) (base:int list) (i:int) <=>
    ((&0:int) <= i /\ i < (&(LENGTH base):int)) /\
    (let y = pair_insert_nth base i in
     pair_insert_single_phase
       original i y (i - (&1:int)) base)`);;

ignore (
 `!a:int list.
    (&0:int) <= (&0:int) /\
    (&0:int) <= (&(LENGTH a):int) /\
    pair_insert_sorted_upto a (&0:int) /\
    pair_insert_permut a a /\
    (!i:int. !a1:int list.
       LENGTH a1 = LENGTH a
       ==>
       (((&0:int) <= i /\ i <= (&(LENGTH a1):int)) /\
        pair_insert_sorted_upto a1 i /\
        pair_insert_permut a a1)
       ==>
       if i < (&(LENGTH a1):int) - (&1:int) then
         pair_insert_pair_case a a1 i
       else if i = (&(LENGTH a1):int) - (&1:int) then
         pair_insert_single_case a a1 i
       else
         pair_insert_sorted_upto a1 (&(LENGTH a1):int) /\
         pair_insert_permut a a1)`);;

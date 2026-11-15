(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/priority_queue_PQueue_selected_partqtvc: a priority-queue
  verification condition connecting aggregate key comparisons with the
  selected branch of a three-way sequence split. This file contains no proof.

  The singleton function field retains the source type index: for every index
  type, ('index -> unit) has exactly one extensional value. Thus
  pqueue_element is a bijective indexed wrapper of the arbitrary source
  element carrier for the quantified type instance.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  pqueue_element = PQueueElement ('index -> unit) 'node
End

Datatype:
  pqueue_split =
    PQueueSplit ('a list) ('a option) ('a list)
End

Datatype:
  pqueue_part =
    PQueueLeft unit
  | PQueueRight unit
  | PQueueHere
End

val pqueue_split_left_def = Define `
  pqueue_split_left (PQueueSplit left middle right) = left`;

val pqueue_split_middle_def = Define `
  pqueue_split_middle (PQueueSplit left middle right) = middle`;

val pqueue_split_right_def = Define `
  pqueue_split_right (PQueueSplit left middle right) = right`;

val pqueue_option_to_seq_def = Define `
  (pqueue_option_to_seq NONE = []) /\
  (pqueue_option_to_seq (SOME element) = [element])`;

val pqueue_rebuild_def = Define `
  pqueue_rebuild split =
    APPEND
      (APPEND
        (pqueue_split_left split)
        (pqueue_option_to_seq (pqueue_split_middle split)))
      (pqueue_split_right split)`;

val pqueue_left_extend_def = Define `
  pqueue_left_extend left element split =
    PQueueSplit
      (APPEND left (element :: pqueue_split_left split))
      (pqueue_split_middle split)
      (pqueue_split_right split)`;

val pqueue_right_extend_def = Define `
  pqueue_right_extend split element right =
    PQueueSplit
      (pqueue_split_left split)
      (pqueue_split_middle split)
      (APPEND (pqueue_split_right split) (element :: right))`;

val pqueue_int_to_num_def = Define `
  pqueue_int_to_num (z : int) = if z < 0 then 0 else Num z`;

val pqueue_key_eq_def = Define `
  pqueue_key_eq (le : 'key -> 'key -> bool) x y <=>
    le x y /\ le y x`;

val pqueue_lt_def = Define `
  pqueue_lt (le : 'key -> 'key -> bool) x y <=>
    le x y /\ ~le y x`;

val pqueue_op_def = Define `
  pqueue_op (le : 'key -> 'key -> bool) x y =
    case x of
      NONE => y
    | SOME a =>
        (case y of
           NONE => x
         | SOME b => if pqueue_lt le b a then y else x)`;

val pqueue_agg_def = Define `
  (pqueue_agg (le : 'key -> 'key -> bool)
      (f : 'a -> 'key option) [] = NONE) /\
  (pqueue_agg le f (element :: elements) =
     pqueue_op le (f element) (pqueue_agg le f elements))`;

val pqueue_measure_def = Define `
  pqueue_measure (key : 'a -> 'key) element = SOME (key element)`;

val pqueue_selection_possible_def = Define `
  pqueue_selection_possible (selector : 'selector)
      (elements : 'a list) <=>
    LENGTH elements <> 0`;

val pqueue_lower_bound_def = Define `
  pqueue_lower_bound (key : 'a -> 'key)
      (le : 'key -> 'key -> bool) lower elements <=>
    !i : int.
      0 <= i /\ i < &(LENGTH elements) ==>
      le lower (key (EL (pqueue_int_to_num i) elements))`;

val pqueue_lower_bound_strict_def = Define `
  pqueue_lower_bound_strict (key : 'a -> 'key)
      (le : 'key -> 'key -> bool) lower elements <=>
    !i : int.
      0 <= i /\ i < &(LENGTH elements) ==>
      pqueue_lt le lower
        (key (EL (pqueue_int_to_num i) elements))`;

val pqueue_selected_def = Define `
  pqueue_selected (key : 'a -> 'key)
      (le : 'key -> 'key -> bool) (selector : 'selector) split <=>
    case pqueue_split_middle split of
      NONE => F
    | SOME element =>
        pqueue_lower_bound key le (key element)
          (pqueue_split_right split) /\
        pqueue_lower_bound_strict key le (key element)
          (pqueue_split_left split)`;

val pqueue_compare_def = Define `
  pqueue_compare (le : 'key -> 'key -> bool) x y (order : int) <=>
    (((0 : int) < order <=> pqueue_lt le x y) /\
     (order < (0 : int) <=> pqueue_lt le y x) /\
     (order = (0 : int) <=> pqueue_key_eq le y x))`;

val priority_queue_PQueue_selected_part_vc =
  ``!(balancing : num)
      (key : (('index, 'node) pqueue_element) -> 'key)
      (le : 'key -> 'key -> bool)
      (d : ('index, 'node) pqueue_element)
      (rseq : (('index, 'node) pqueue_element) list)
      (lseq : (('index, 'node) pqueue_element) list).
      (0 : int) < &balancing ==>
      (!x. le x x) ==>
      (!x y z. le x y /\ le y z ==> le x z) ==>
      (!x y. le x y \/ le y x) ==>
      (!a b c.
         pqueue_op le a (pqueue_op le b c) =
         pqueue_op le (pqueue_op le a b) c) ==>
      (!x.
         pqueue_op le x NONE = x /\
         x = pqueue_op le NONE x) ==>
      let kd = key d in
        (case pqueue_agg le (pqueue_measure key) rseq of
           NONE =>
             (case pqueue_agg le (pqueue_measure key) lseq of
                NONE => T
              | SOME x => T)
         | SOME x =>
             (case pqueue_agg le (pqueue_measure key) lseq of
                NONE => T
              | SOME x1 => T)) /\
        !result : pqueue_part.
          (case pqueue_agg le (pqueue_measure key) rseq of
             NONE =>
               (case pqueue_agg le (pqueue_measure key) lseq of
                  NONE => result = PQueueHere
                | SOME x =>
                    ?o1 : int.
                      pqueue_compare le x kd o1 /\
                      (if o1 < (0 : int)
                       then result = PQueueHere
                       else result = PQueueLeft ()))
           | SOME x =>
               (case pqueue_agg le (pqueue_measure key) lseq of
                  NONE =>
                    ?o1 : int.
                      pqueue_compare le x kd o1 /\
                      (if o1 <= (0 : int)
                       then result = PQueueHere
                       else result = PQueueRight ())
                | SOME x1 =>
                    ?o1 : int.
                      pqueue_compare le x kd o1 /\
                      (if o1 <= (0 : int) then
                         ?o2 : int.
                           pqueue_compare le kd x1 o2 /\
                           (if o2 <= (0 : int)
                            then result = PQueueLeft ()
                            else result = PQueueHere)
                       else
                         ?o2 : int.
                           pqueue_compare le x x1 o2 /\
                           (if o2 <= (0 : int)
                            then result = PQueueLeft ()
                            else result = PQueueRight ()))))
          ==>
          (case result of
             PQueueHere =>
               pqueue_selected key le ()
                 (PQueueSplit lseq (SOME d) rseq)
           | PQueueLeft rsl =>
               pqueue_selection_possible rsl lseq /\
               !split.
                 pqueue_selected key le rsl split /\
                 pqueue_rebuild split = lseq ==>
                 pqueue_selected key le ()
                   (pqueue_right_extend split d rseq)
           | PQueueRight rsr =>
               pqueue_selection_possible rsr rseq /\
               !split.
                 pqueue_selected key le rsr split /\
                 pqueue_rebuild split = rseq ==>
                 pqueue_selected key le ()
                   (pqueue_left_extend lseq d split))``;

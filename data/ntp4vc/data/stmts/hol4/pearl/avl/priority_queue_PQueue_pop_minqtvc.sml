(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/priority_queue_PQueue_pop_minqtvc: a priority-queue pop-minimum
  verification condition preserving cardinality and multiplicities after
  removing a selected minimum with bounded AVL height change. This file
  contains no proof.

  The singleton function fields retain the source type index: for every index
  type, ('index -> unit) has exactly one extensional value. Thus
  pqueue_element and pqueue_object are bijective indexed wrappers of their
  arbitrary underlying carriers for the quantified source type instance.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  pqueue_element = PQueueElement ('index -> unit) 'node
End

Datatype:
  pqueue_object = PQueueObject ('index -> unit) 'carrier
End

Datatype:
  pqueue_tree =
    PQueueEmpty
  | PQueueNode pqueue_tree
      (('index, 'node) pqueue_element)
      pqueue_tree num ('key option)
End

Datatype:
  pqueue_model =
    PQueueModel ((('index, 'node) pqueue_element) list) int
End

Datatype:
  pqueue_split =
    PQueueSplit ('a list) ('a option) ('a list)
End

Datatype:
  pqueue_summary =
    PQueueSummary ('a -> int) 'a int
End

val pqueue_model_seq_def = Define `
  pqueue_model_seq (PQueueModel elements height) = elements`;

val pqueue_model_hgt_def = Define `
  pqueue_model_hgt (PQueueModel elements height) = height`;

val pqueue_split_left_def = Define `
  pqueue_split_left (PQueueSplit left middle right) = left`;

val pqueue_split_middle_def = Define `
  pqueue_split_middle (PQueueSplit left middle right) = middle`;

val pqueue_split_right_def = Define `
  pqueue_split_right (PQueueSplit left middle right) = right`;

val pqueue_summary_bag_def = Define `
  pqueue_summary_bag (PQueueSummary bag minimum card) = bag`;

val pqueue_summary_minimum_def = Define `
  pqueue_summary_minimum (PQueueSummary bag minimum card) = minimum`;

val pqueue_summary_card_def = Define `
  pqueue_summary_card (PQueueSummary bag minimum card) = card`;

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

val pqueue_int_to_num_def = Define `
  pqueue_int_to_num (z : int) = if z < 0 then 0 else Num z`;

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
  pqueue_selection_possible (elements : 'a list) <=>
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
      (le : 'key -> 'key -> bool) split <=>
    case pqueue_split_middle split of
      NONE => F
    | SOME element =>
        pqueue_lower_bound key le (key element)
          (pqueue_split_right split) /\
        pqueue_lower_bound_strict key le (key element)
          (pqueue_split_left split)`;

val pqueue_seq_model_def = Define `
  (pqueue_seq_model PQueueEmpty = []) /\
  (pqueue_seq_model
      (PQueueNode left root right height summary) =
     APPEND (pqueue_seq_model left)
       (root :: pqueue_seq_model right))`;

val pqueue_real_height_def = Define `
  (pqueue_real_height PQueueEmpty = (0 : int)) /\
  (pqueue_real_height
      (PQueueNode left root right height summary) =
     1 +
       (if pqueue_real_height left < pqueue_real_height right
        then pqueue_real_height right
        else pqueue_real_height left))`;

val pqueue_balanced_def = Define `
  (pqueue_balanced balancing key le PQueueEmpty = T) /\
  (pqueue_balanced balancing key le
      (PQueueNode left root right height summary) =
     (&height =
        pqueue_real_height
          (PQueueNode left root right height summary) /\
      summary =
        pqueue_agg le (pqueue_measure key)
          (pqueue_seq_model
            (PQueueNode left root right height summary)) /\
      -(&balancing) <=
        pqueue_real_height right - pqueue_real_height left /\
      pqueue_real_height right - pqueue_real_height left <=
        &balancing /\
      pqueue_balanced balancing key le left /\
      pqueue_balanced balancing key le right))`;

val pqueue_to_bag_def = Define `
  pqueue_to_bag (elements : 'a list) element =
    &(LENGTH (FILTER (\candidate. candidate = element) elements))`;

val pqueue_m3_def = Define `
  pqueue_m3 get_minimum_index m1 object =
    let elements = pqueue_model_seq (m1 object) in
      PQueueSummary
        (pqueue_to_bag elements)
        (EL
          (pqueue_int_to_num (get_minimum_index elements))
          elements)
        (&(LENGTH elements))`;

val priority_queue_PQueue_pop_min_vc =
  ``!(balancing : num)
      (key : (('index, 'node) pqueue_element) -> 'key)
      (le : 'key -> 'key -> bool)
      (repr :
        (('index, 'carrier) pqueue_object) ->
        ('index, 'key, 'node) pqueue_tree)
      (m1 :
        (('index, 'carrier) pqueue_object) ->
        ('index, 'node) pqueue_model)
      (get_minimum_index :
        (('index, 'node) pqueue_element) list -> int)
      (t5 : ('index, 'carrier) pqueue_object).
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
      (!self.
         pqueue_balanced balancing key le (repr self) /\
         pqueue_model_seq (m1 self) =
           pqueue_seq_model (repr self) /\
         pqueue_model_hgt (m1 self) =
           pqueue_real_height (repr self)) ==>
      (!a b.
         repr a = repr b /\ m1 a = m1 b ==>
         a = b) ==>
      (!elements.
         LENGTH elements <> 0 ==>
         0 <= get_minimum_index elements /\
         get_minimum_index elements < &(LENGTH elements)) ==>
      (!elements.
         LENGTH elements <> 0 ==>
         pqueue_agg le (pqueue_measure key) elements =
           SOME
             (key
               (EL
                 (pqueue_int_to_num
                   (get_minimum_index elements))
                 elements))) ==>
      (!elements.
         LENGTH elements <> 0 ==>
         pqueue_lower_bound_strict key le
           (key
             (EL
               (pqueue_int_to_num
                 (get_minimum_index elements))
               elements))
           (TAKE
             (pqueue_int_to_num (get_minimum_index elements))
             elements)) ==>
      (!elements.
         LENGTH elements <> 0 ==>
         pqueue_lower_bound key le
           (key
             (EL
               (pqueue_int_to_num
                 (get_minimum_index elements))
               elements))
           (DROP
             (pqueue_int_to_num (get_minimum_index elements))
             elements)) ==>
      (0 : int) <
        pqueue_summary_card
          (pqueue_m3 get_minimum_index m1 t5) ==>
      pqueue_selection_possible
        (pqueue_model_seq (m1 t5)) /\
      !split result.
        pqueue_model_seq (m1 result) =
          APPEND
            (pqueue_split_left split)
            (pqueue_split_right split) /\
        (pqueue_selected key le split /\
         pqueue_rebuild split =
           pqueue_model_seq (m1 t5)) /\
        pqueue_model_hgt (m1 t5) -
          pqueue_model_hgt (m1 result) <= (1 : int) /\
        (0 : int) <=
          pqueue_model_hgt (m1 t5) -
            pqueue_model_hgt (m1 result) ==>
        pqueue_summary_card
          (pqueue_m3 get_minimum_index m1 t5) =
          pqueue_summary_card
            (pqueue_m3 get_minimum_index m1 result) +
          (1 : int) /\
        pqueue_summary_bag
          (pqueue_m3 get_minimum_index m1 t5)
          (pqueue_summary_minimum
            (pqueue_m3 get_minimum_index m1 t5)) =
          pqueue_summary_bag
            (pqueue_m3 get_minimum_index m1 result)
            (pqueue_summary_minimum
              (pqueue_m3 get_minimum_index m1 t5)) +
          (1 : int) /\
        !element.
          element <>
            pqueue_summary_minimum
              (pqueue_m3 get_minimum_index m1 t5) ==>
          pqueue_summary_bag
            (pqueue_m3 get_minimum_index m1 t5) element =
          pqueue_summary_bag
            (pqueue_m3 get_minimum_index m1 result) element``;

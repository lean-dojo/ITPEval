(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/priority_queue_PQueue_minqtvc: a priority-queue minimum
  verification condition relating nonemptiness, selected minima, bag
  multiplicity, and the stored minimum. This file contains no proof.
*)

let pqueue_min_tree_INDUCT,pqueue_min_tree_RECURSION =
  define_type
    "pqueue_min_tree =
       PQueueMinEmpty
     | PQueueMinNode pqueue_min_tree A pqueue_min_tree num (K option)";;

let statement =
 `!balancing:num.
  !key:A->K.
  !le:K->K->bool.
  !agg:(A->K option)->A list->K option.
  !measure_closure:A->K option.
  !seq_model:(A,K)pqueue_min_tree->A list.
  !real_height:(A,K)pqueue_min_tree->int.
  !balanced:(A,K)pqueue_min_tree->bool.
  !repr:Q->(A,K)pqueue_min_tree.
  !m1:Q->A list#int.
  !to_bag:A list->A->int.
  !get_minimum_index:A list->int.
  !t5:Q.
    let lt = \(x:K) (y:K). le x y /\ ~le y x in
    let op =
      \(x:K option) (y:K option).
        if x = NONE then y
        else if y = NONE then x
        else
          let a = @a. x = SOME a in
          let b = @b. y = SOME b in
          if lt b a then y else x in
    let seq = \x:Q. FST (m1 x) in
    let hgt = \x:Q. SND (m1 x) in
    let split_left =
      \((left:A list),(middle:A option),(right:A list)). left in
    let split_middle =
      \((left:A list),(middle:A option),(right:A list)). middle in
    let split_right =
      \((left:A list),(middle:A option),(right:A list)). right in
    let option_to_seq =
      \middle:A option.
        if middle = NONE then []
        else [@datum. middle = SOME datum] in
    let rebuild =
      \parts:A list#A option#A list.
        APPEND
          (APPEND (split_left parts)
                  (option_to_seq (split_middle parts)))
          (split_right parts) in
    let lower_bound =
      \(x:K) (values:A list).
        !i:int.
          (&0:int) <= i /\ i < (&(LENGTH values):int)
          ==> le x (key (EL (num_of_int i) values)) in
    let lower_bound_strict =
      \(x:K) (values:A list).
        !i:int.
          (&0:int) <= i /\ i < (&(LENGTH values):int)
          ==> lt x (key (EL (num_of_int i) values)) in
    let selected =
      \parts:A list#A option#A list.
        let middle = split_middle parts in
        if middle = NONE then F
        else
          let datum = @datum. middle = SOME datum in
          lower_bound (key datum) (split_right parts) /\
          lower_bound_strict (key datum) (split_left parts) in
    let selection_possible =
      \values:A list. ~((&(LENGTH values):int) = (&0:int)) in
    let model =
      \queue:Q.
        (to_bag (seq queue),
         EL (num_of_int (get_minimum_index (seq queue))) (seq queue),
         (&(LENGTH (seq queue)):int)) in
    let bag =
      \((multiplicity:A->int),(minimum:A),(cardinality:int)).
        multiplicity in
    let minimum =
      \((multiplicity:A->int),(minimum:A),(cardinality:int)).
        minimum in
    let card =
      \((multiplicity:A->int),(minimum:A),(cardinality:int)).
        cardinality in
    let option_payload =
      \chosen:A option. @datum. chosen = SOME datum in
    let conclusion =
      (selection_possible (seq t5) /\
       (!parts:A list#A option#A list.
        !chosen:A option.
          ((selected parts /\ rebuild parts = seq t5) /\
           split_middle parts = chosen)
          ==>
          ~(chosen = NONE) /\
          (!result:A.
             (if chosen = NONE then F
              else result = option_payload chosen)
             ==>
             ((&0:int) < bag (model t5) result /\
              result = minimum (model t5))))) in
    let background =
      (0 < balancing /\
       (!x:K. le x x) /\
       (!x y z:K. le x y /\ le y z ==> le x z) /\
       (!x y:K. le x y \/ le y x) /\
       (!a b c:K option.
          op a (op b c) = op (op a b) c) /\
       (!x:K option.
          op x NONE = x /\ x = op NONE x) /\
       (!f:A->K option. agg f [] = NONE) /\
       (!f:A->K option.
        !datum:A.
        !tail:A list.
          agg f (CONS datum tail) =
            op (f datum) (agg f tail)) /\
       (!datum:A.
          measure_closure datum = SOME (key datum)) /\
       seq_model PQueueMinEmpty = [] /\
       (!left_tree:(A,K)pqueue_min_tree.
        !datum:A.
        !right_tree:(A,K)pqueue_min_tree.
        !height:num.
        !summary:K option.
          seq_model
            (PQueueMinNode
              left_tree datum right_tree height summary) =
          APPEND
            (seq_model left_tree)
            (CONS datum (seq_model right_tree))) /\
       real_height PQueueMinEmpty = (&0:int) /\
       (!left_tree:(A,K)pqueue_min_tree.
        !datum:A.
        !right_tree:(A,K)pqueue_min_tree.
        !height:num.
        !summary:K option.
          real_height
            (PQueueMinNode
              left_tree datum right_tree height summary) =
          (&1:int) +
          (if real_height left_tree < real_height right_tree
           then real_height right_tree
           else real_height left_tree)) /\
       balanced PQueueMinEmpty /\
       (!left_tree:(A,K)pqueue_min_tree.
        !datum:A.
        !right_tree:(A,K)pqueue_min_tree.
        !height:num.
        !summary:K option.
          (balanced
             (PQueueMinNode
               left_tree datum right_tree height summary) <=>
           (&height:int) =
             real_height
               (PQueueMinNode
                 left_tree datum right_tree height summary) /\
           summary =
             agg measure_closure
               (seq_model
                 (PQueueMinNode
                   left_tree datum right_tree height summary)) /\
           (--(&balancing:int) <=
              real_height right_tree - real_height left_tree /\
            real_height right_tree - real_height left_tree <=
              (&balancing:int)) /\
           balanced left_tree /\ balanced right_tree)) /\
       (!self:Q.
          balanced (repr self) /\
          seq self = seq_model (repr self) /\
          hgt self = real_height (repr self)) /\
       (!left right:Q.
          repr left = repr right /\ m1 left = m1 right
          ==> left = right) /\
       (!values:A list.
        !datum:A.
          to_bag values datum =
            (&(LENGTH (FILTER (\x:A. x = datum) values)):int)) /\
       (!values:A list.
          selection_possible values
          ==>
          let index = get_minimum_index values in
          (&0:int) <= index /\
          index < (&(LENGTH values):int) /\
          agg measure_closure values =
            SOME (key (EL (num_of_int index) values)) /\
          (!i:int.
             (&0:int) <= i /\ i < index
             ==> lt
                   (key (EL (num_of_int index) values))
                   (key (EL (num_of_int i) values))) /\
          (!i:int.
             index <= i /\ i < (&(LENGTH values):int)
                 ==> le
                   (key (EL (num_of_int index) values))
                   (key (EL (num_of_int i) values))))) in
    background
    ==> ((&0:int) < card (model t5))
    ==> conclusion`;;

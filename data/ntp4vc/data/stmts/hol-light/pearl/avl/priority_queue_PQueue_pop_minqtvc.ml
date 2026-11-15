(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/priority_queue_PQueue_pop_minqtvc: a priority-queue pop-min
  verification condition relating selected minimum removal, bag
  multiplicities, cardinality, and bounded height decrease.
  This file contains no proof.
*)

let pqueue_pop_min_tree_INDUCT,pqueue_pop_min_tree_RECURSION =
  define_type
    "pqueue_pop_min_tree =
       PQueuePopMinEmpty
     | PQueuePopMinNode
         pqueue_pop_min_tree A pqueue_pop_min_tree num (K option)";;

let statement =
 `!balancing:num.
  !key:A->K.
  !le:K->K->bool.
  !lt:K->K->bool.
  !op:K option->K option->K option.
  !agg:(A->K option)->A list->K option.
  !measure_closure:A->K option.
  !selection_possible:A list->bool.
  !split_left:(A list#A option#A list)->A list.
  !split_middle:(A list#A option#A list)->A option.
  !split_right:(A list#A option#A list)->A list.
  !rebuild:(A list#A option#A list)->A list.
  !lower_bound:K->A list->bool.
  !lower_bound_strict:K->A list->bool.
  !selected:(A list#A option#A list)->bool.
  !seq_model:(A,K)pqueue_pop_min_tree->A list.
  !real_height:(A,K)pqueue_pop_min_tree->int.
  !balanced:(A,K)pqueue_pop_min_tree->bool.
  !repr:Q->(A,K)pqueue_pop_min_tree.
  !m1:Q->A list#int.
  !to_bag:A list->A->int.
  !get_minimum_index:A list->int.
  !t5:Q.
    (0 < balancing /\
       (!x:K. le x x) /\
       (!x y z:K. le x y /\ le y z ==> le x z) /\
       (!x y:K. le x y \/ le y x) /\
       (!x y:K. lt x y <=> le x y /\ ~le y x) /\
       (!x y:K option.
          op x y =
            if x = NONE then y
            else if y = NONE then x
            else
              let a = @a. x = SOME a in
              let b = @b. y = SOME b in
              if lt b a then y else x) /\
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
       (!values:A list.
          selection_possible values <=>
          ~((&(LENGTH values):int) = (&0:int))) /\
       (!left:A list.
        !middle:A option.
        !right:A list.
          split_left (left,middle,right) = left /\
          split_middle (left,middle,right) = middle /\
          split_right (left,middle,right) = right) /\
       (!parts:A list#A option#A list.
          rebuild parts =
            APPEND
              (APPEND
                (split_left parts)
                (if split_middle parts = NONE then []
                 else [@datum. split_middle parts = SOME datum]))
              (split_right parts)) /\
       (!x:K.
        !values:A list.
          (lower_bound x values <=>
           (!i:int.
              (&0:int) <= i /\ i < (&(LENGTH values):int)
              ==> le x (key (EL (num_of_int i) values))))) /\
       (!x:K.
        !values:A list.
          (lower_bound_strict x values <=>
           (!i:int.
              (&0:int) <= i /\ i < (&(LENGTH values):int)
              ==> lt x (key (EL (num_of_int i) values))))) /\
       (!parts:A list#A option#A list.
          (selected parts <=>
           if split_middle parts = NONE then F
           else
             let datum = @datum. split_middle parts = SOME datum in
             lower_bound (key datum) (split_right parts) /\
             lower_bound_strict (key datum) (split_left parts))) /\
       seq_model PQueuePopMinEmpty = [] /\
       (!left_tree:(A,K)pqueue_pop_min_tree.
        !datum:A.
        !right_tree:(A,K)pqueue_pop_min_tree.
        !height:num.
        !summary:K option.
          seq_model
            (PQueuePopMinNode
              left_tree datum right_tree height summary) =
          APPEND
            (seq_model left_tree)
            (CONS datum (seq_model right_tree))) /\
       real_height PQueuePopMinEmpty = (&0:int) /\
       (!left_tree:(A,K)pqueue_pop_min_tree.
        !datum:A.
        !right_tree:(A,K)pqueue_pop_min_tree.
        !height:num.
        !summary:K option.
          real_height
            (PQueuePopMinNode
              left_tree datum right_tree height summary) =
          (&1:int) +
          (if real_height left_tree < real_height right_tree
           then real_height right_tree
           else real_height left_tree)) /\
       balanced PQueuePopMinEmpty /\
       (!left_tree:(A,K)pqueue_pop_min_tree.
        !datum:A.
        !right_tree:(A,K)pqueue_pop_min_tree.
        !height:num.
        !summary:K option.
          (balanced
             (PQueuePopMinNode
               left_tree datum right_tree height summary) <=>
           (&height:int) =
             real_height
               (PQueuePopMinNode
                 left_tree datum right_tree height summary) /\
           summary =
             agg measure_closure
               (seq_model
                 (PQueuePopMinNode
                   left_tree datum right_tree height summary)) /\
           (--(&balancing:int) <=
              real_height right_tree - real_height left_tree /\
            real_height right_tree - real_height left_tree <=
              (&balancing:int)) /\
           balanced left_tree /\ balanced right_tree)) /\
       (!self:Q.
          balanced (repr self) /\
          FST (m1 self) = seq_model (repr self) /\
          SND (m1 self) = real_height (repr self)) /\
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
          (&0:int) <= get_minimum_index values /\
          get_minimum_index values < (&(LENGTH values):int) /\
          agg measure_closure values =
            SOME
              (key
                (EL
                  (num_of_int (get_minimum_index values))
                  values)) /\
          lower_bound_strict
            (key
              (EL
                (num_of_int (get_minimum_index values))
                values))
            (TAKE (num_of_int (get_minimum_index values)) values) /\
          lower_bound
            (key
              (EL
                (num_of_int (get_minimum_index values))
                values))
            (DROP (num_of_int (get_minimum_index values)) values)))
    ==>
    ((&0:int) < (&(LENGTH (FST (m1 t5))):int))
    ==>
    selection_possible (FST (m1 t5)) /\
    (!parts:A list#A option#A list.
     !remaining:Q.
       FST (m1 remaining) =
         APPEND (split_left parts) (split_right parts) /\
       (selected parts /\ rebuild parts = FST (m1 t5)) /\
       SND (m1 t5) - SND (m1 remaining) <= (&1:int) /\
       (&0:int) <= SND (m1 t5) - SND (m1 remaining)
       ==>
       (&(LENGTH (FST (m1 t5))):int) =
         (&(LENGTH (FST (m1 remaining))):int) + (&1:int) /\
       to_bag (FST (m1 t5))
         (EL
           (num_of_int (get_minimum_index (FST (m1 t5))))
           (FST (m1 t5))) =
         to_bag (FST (m1 remaining))
           (EL
             (num_of_int (get_minimum_index (FST (m1 t5))))
             (FST (m1 t5))) + (&1:int) /\
       (!other:A.
          ~(other =
            EL
              (num_of_int (get_minimum_index (FST (m1 t5))))
              (FST (m1 t5)))
          ==> to_bag (FST (m1 t5)) other =
              to_bag (FST (m1 remaining)) other))`;;

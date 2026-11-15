(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/priority_queue_PQueue_selected_partqtvc: a priority-queue
  verification condition selecting the current datum, the left subsequence,
  or the right subsequence according to their aggregate keys. This file
  contains no proof.
*)

let pqueue_selected_part_INDUCT,pqueue_selected_part_RECURSION =
  define_type
    "pqueue_selected_part =
       PQueueSelectedHere
     | PQueueSelectedLeft
     | PQueueSelectedRight";;

let statement =
 `!balancing:num.
  !key:A->K.
  !le:K->K->bool.
  !agg:(A->K option)->A list->K option.
  !measure_closure:A->K option.
  !d:A.
  !rseq:A list.
  !lseq:A list.
    let key_eq = \(x:K) (y:K). le x y /\ le y x in
    let key_lt = \(x:K) (y:K). le x y /\ ~le y x in
    let op =
      \(x:K option) (y:K option).
        if x = NONE then y
        else if y = NONE then x
        else
          let a = @a. x = SOME a in
          let b = @b. y = SOME b in
          if key_lt b a then y else x in
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
    let left_extend =
      \(left:A list) (datum:A)
       (parts:A list#A option#A list).
        (APPEND left (CONS datum (split_left parts)),
         split_middle parts,
         split_right parts) in
    let right_extend =
      \(parts:A list#A option#A list) (datum:A)
       (right:A list).
        (split_left parts,
         split_middle parts,
         APPEND (split_right parts) (CONS datum right)) in
    let lower_bound =
      \(x:K) (values:A list).
        !i:int.
          (&0:int) <= i /\ i < (&(LENGTH values):int)
          ==> le x (key (EL (num_of_int i) values)) in
    let lower_bound_strict =
      \(x:K) (values:A list).
        !i:int.
          (&0:int) <= i /\ i < (&(LENGTH values):int)
          ==> key_lt x (key (EL (num_of_int i) values)) in
    let selected =
      \(_selector:1) (parts:A list#A option#A list).
        let middle = split_middle parts in
        if middle = NONE then F
        else
          let datum = @datum. middle = SOME datum in
          lower_bound (key datum) (split_right parts) /\
          lower_bound_strict (key datum) (split_left parts) in
    let selection_possible =
      \(_selector:1) (values:A list).
        ~((&(LENGTH values):int) = (&0:int)) in
    let option_payload =
      \value:K option. @x. value = SOME x in
    let comparison =
      \(x:K) (y:K) (order:int).
        (((&0:int) < order <=> key_lt x y) /\
         (order < (&0:int) <=> key_lt y x) /\
         (order = (&0:int) <=> key_eq y x)) in
    let kd = key d in
    let right_aggregate = agg measure_closure rseq in
    let left_aggregate = agg measure_closure lseq in
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
          measure_closure datum = SOME (key datum))) in
    let branch_precondition =
      \result:pqueue_selected_part.
        (right_aggregate = NONE /\
         ((left_aggregate = NONE /\
           result = PQueueSelectedHere) \/
          (~(left_aggregate = NONE) /\
           (let x = option_payload left_aggregate in
            ?o1:int.
              comparison x kd o1 /\
              ((o1 < (&0:int) /\
                result = PQueueSelectedHere) \/
               (~(o1 < (&0:int)) /\
                result = PQueueSelectedLeft))))) \/
        (~(right_aggregate = NONE) /\
         (let x = option_payload right_aggregate in
          (left_aggregate = NONE /\
           (?o1:int.
              comparison x kd o1 /\
              ((o1 <= (&0:int) /\
                result = PQueueSelectedHere) \/
               (~(o1 <= (&0:int)) /\
                result = PQueueSelectedRight)))) \/
          (~(left_aggregate = NONE) /\
           (let x1 = option_payload left_aggregate in
            ?o1:int.
              comparison x kd o1 /\
              ((o1 <= (&0:int) /\
                (?o2:int.
                   comparison kd x1 o2 /\
                   ((o2 <= (&0:int) /\
                     result = PQueueSelectedLeft) \/
                    (~(o2 <= (&0:int)) /\
                     result = PQueueSelectedHere)))) \/
               (~(o1 <= (&0:int)) /\
                (?o2:int.
                   comparison x x1 o2 /\
                   ((o2 <= (&0:int) /\
                    result = PQueueSelectedLeft) \/
                    (~(o2 <= (&0:int)) /\
                     result = PQueueSelectedRight)))))))))) in
    let branch_conclusion =
      \result:pqueue_selected_part.
        (result = PQueueSelectedHere /\
         selected one (lseq,SOME d,rseq)) \/
        (result = PQueueSelectedLeft /\
         selection_possible one lseq /\
         (!parts:A list#A option#A list.
            selected one parts /\ rebuild parts = lseq
            ==> selected one (right_extend parts d rseq))) \/
        (result = PQueueSelectedRight /\
         selection_possible one rseq /\
         (!parts:A list#A option#A list.
            selected one parts /\ rebuild parts = rseq
            ==> selected one (left_extend lseq d parts))) in
    background
    ==>
    ((COND (right_aggregate = NONE)
        (COND (left_aggregate = NONE) T T)
        (COND (left_aggregate = NONE) T T)) /\
     (!result:pqueue_selected_part.
        branch_precondition result
        ==> branch_conclusion result))`;;

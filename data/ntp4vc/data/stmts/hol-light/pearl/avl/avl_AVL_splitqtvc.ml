(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/avl_AVL_splitqtvc: an AVL-tree split verification condition for
  selector-guided decomposition, recursive left and right splitting, sequence
  reconstruction, and bounded cached-height adjustment. This file contains
  no proof.
*)

let avl_split_tree_INDUCT,avl_split_tree_RECURSION = define_type
  "avl_split_tree =
       AvlSplitEmpty
     | AvlSplitNode avl_split_tree A avl_split_tree num C";;

let statement =
 `!zero:C.
  !op:C->C->C.
  !agg:(A->C)->A list->C.
  !measure:A->C.
  !balancing:num.
  !measure_closure:A->C.
  !seq_model:(A,C)avl_split_tree->A list.
  !real_height:(A,C)avl_split_tree->int.
  !balanced:(A,C)avl_split_tree->bool.
  !repr:B->(A,C)avl_split_tree.
  !m1:B->A list#int.
  !selected:D->(A list#A option#A list)->bool.
  !selection_possible:D->A list->bool.
  !s:D.
  !t3:B.
  !o1:(B#A#B#num#C)option.
    let node_model =
      \(left:A list) (datum:A) (right:A list).
        APPEND left (CONS datum right) in
    let seq = \x:B. FST (m1 x) in
    let hgt = \x:B. SND (m1 x) in
    let split_make =
      \(left:A list) (middle:A option) (right:A list).
        (left,middle,right) in
    let split_left =
      \((left:A list),(middle:A option),(right:A list)). left in
    let split_middle =
      \((left:A list),(middle:A option),(right:A list)). middle in
    let split_right =
      \((left:A list),(middle:A option),(right:A list)). right in
    let option_payload =
      \choice:A option. @datum. choice = SOME datum in
    let option_to_seq =
      \middle:A option.
        COND (middle = NONE) [] [option_payload middle] in
    let rebuild =
      \parts:A list#A option#A list.
        APPEND
          (APPEND (split_left parts)
                  (option_to_seq (split_middle parts)))
          (split_right parts) in
    let left_extend =
      \(left:A list) (datum:A) (parts:A list#A option#A list).
        split_make
          (APPEND left (CONS datum (split_left parts)))
          (split_middle parts)
          (split_right parts) in
    let right_extend =
      \(parts:A list#A option#A list) (datum:A) (right:A list).
        split_make
          (split_left parts)
          (split_middle parts)
          (APPEND (split_right parts) (CONS datum right)) in
    let view_payload =
      \view:(B#A#B#num#C)option. @p. view = SOME p in
    let view_left =
      \((left:B),(datum:A),(right:B),(height:num),(summary:C)).
        left in
    let view_datum =
      \((left:B),(datum:A),(right:B),(height:num),(summary:C)).
        datum in
    let view_right =
      \((left:B),(datum:A),(right:B),(height:num),(summary:C)).
        right in
    let view_height =
      \((left:B),(datum:A),(right:B),(height:num),(summary:C)).
        height in
    let view_summary =
      \((left:B),(datum:A),(right:B),(height:num),(summary:C)).
        summary in
    let branch_payload =
      \branch:(bool#D)option. @p. branch = SOME p in
    let middle_matches =
      \(choice:A option) (parts:A list#A option#A list).
        COND (choice = NONE)
          (split_middle parts = NONE)
          (split_middle parts = SOME (option_payload choice)) in
    let within =
      \(left:B) (right:B).
        --(&balancing:int) <= hgt left - hgt right /\
        hgt left - hgt right <= (&balancing:int) in
    let height_close =
      \(left:B) (right:B) (result:B).
        let expected =
          (&1:int) +
          COND (hgt left < hgt right) (hgt right) (hgt left) in
        let result_height = hgt result in
        (&0:int) <= expected - result_height /\
        expected - result_height <= (&1:int) in
    let empty_split =
      split_make ([]:A list) (NONE:A option) ([]:A list) in
    let view_fact =
      COND (o1 = NONE)
        (hgt t3 = (&0:int) /\ seq t3 = [])
        (let p = view_payload o1 in
         let left = view_left p in
         let datum = view_datum p in
         let right = view_right p in
         let height = view_height p in
         let summary = view_summary p in
         seq t3 = node_model (seq left) datum (seq right) /\
         summary = agg measure_closure (seq t3) /\
         within left right /\
         hgt t3 = (&height:int) /\
         (&height:int) =
           (&1:int) +
           COND (hgt left < hgt right) (hgt right) (hgt left)) in
    let split_result =
      \(parts:A list#A option#A list) (left_result:B)
       (choice:A option) (right_result:B).
        (selected s parts /\ rebuild parts = seq t3) /\
        seq left_result = split_left parts /\
        seq right_result = split_right parts /\
        middle_matches choice parts in
    let part_premise =
      \(branch:(bool#D)option) (left_values:A list)
       (datum:A) (right_values:A list).
        COND (branch = NONE)
          (selected s
             (split_make left_values (SOME datum) right_values))
          (let p = branch_payload branch in
           let subselector = SND p in
           COND (FST p)
             (selection_possible subselector right_values /\
              (!parts:A list#A option#A list.
                 selected subselector parts /\
                 rebuild parts = right_values
                 ==> selected s
                       (left_extend left_values datum parts)))
             (selection_possible subselector left_values /\
              (!parts:A list#A option#A list.
                 selected subselector parts /\
                 rebuild parts = left_values
                 ==> selected s
                       (right_extend parts datum right_values)))) in
    let part_conclusion =
      \(branch:(bool#D)option) (left:B) (datum:A) (right:B).
        COND (branch = NONE)
          (split_result
             (split_make (seq left) (SOME datum) (seq right))
             left (SOME datum) right)
          (let p = branch_payload branch in
           let subselector = SND p in
           COND (FST p)
             ((((&0:int) <= hgt t3 /\ hgt right < hgt t3) /\
               selection_possible subselector (seq right)) /\
              (!parts:A list#A option#A list.
               !right_left:B.
               !choice:A option.
               !right_right:B.
                 (selected subselector parts /\
                  rebuild parts = seq right) /\
                 seq right_left = split_left parts /\
                 seq right_right = split_right parts /\
                 middle_matches choice parts
                 ==> !result:B.
                       seq result =
                         node_model
                           (seq left) datum (seq right_left) /\
                       height_close left right_left result
                       ==> split_result
                             (left_extend (seq left) datum parts)
                             result choice right_right))
             ((((&0:int) <= hgt t3 /\ hgt left < hgt t3) /\
               selection_possible subselector (seq left)) /\
              (!parts:A list#A option#A list.
               !left_left:B.
               !choice:A option.
               !left_right:B.
                 (selected subselector parts /\
                  rebuild parts = seq left) /\
                 seq left_left = split_left parts /\
                 seq left_right = split_right parts /\
                 middle_matches choice parts
                 ==> !result:B.
                       seq result =
                         node_model
                           (seq left_right) datum (seq right) /\
                       height_close left_right right result
                       ==> split_result
                             (right_extend parts datum (seq right))
                             left_left choice result))) in
    let conclusion =
      COND (o1 = NONE)
        (split_result empty_split t3 (NONE:A option) t3)
        (let p = view_payload o1 in
         let left = view_left p in
         let datum = view_datum p in
         let right = view_right p in
         let left_values = seq left in
         let right_values = seq right in
         (selection_possible s
            (node_model left_values datum right_values) /\
          agg measure_closure (seq left) =
            agg measure_closure left_values /\
          agg measure_closure (seq right) =
            agg measure_closure right_values) /\
         (!branch:(bool#D)option.
            part_premise branch left_values datum right_values
            ==> part_conclusion branch left datum right)) in
    let background =
      ((!a b c:C. op a (op b c) = op (op a b) c) /\
       (!x:C. op x zero = x /\ x = op zero x) /\
       (!f:A->C. agg f [] = zero) /\
       (!values:A list.
        !f:A->C.
          (&(LENGTH values):int) = (&1:int)
          ==> agg f values = f (EL 0 values)) /\
       (!f:A->C.
        !left_values right_values:A list.
          agg f (APPEND left_values right_values) =
            op (agg f left_values) (agg f right_values)) /\
       (!datum:A. measure_closure datum = measure datum) /\
       seq_model AvlSplitEmpty = [] /\
       (!left_tree:(A,C)avl_split_tree.
        !datum:A.
        !right_tree:(A,C)avl_split_tree.
        !height:num.
        !summary:C.
          seq_model
            (AvlSplitNode
              left_tree datum right_tree height summary) =
          node_model
            (seq_model left_tree) datum (seq_model right_tree)) /\
       real_height AvlSplitEmpty = (&0:int) /\
       (!left_tree:(A,C)avl_split_tree.
        !datum:A.
        !right_tree:(A,C)avl_split_tree.
        !height:num.
        !summary:C.
          real_height
            (AvlSplitNode
              left_tree datum right_tree height summary) =
          (&1:int) +
          COND (real_height left_tree < real_height right_tree)
            (real_height right_tree) (real_height left_tree)) /\
       balanced AvlSplitEmpty /\
       (!left_tree:(A,C)avl_split_tree.
        !datum:A.
        !right_tree:(A,C)avl_split_tree.
        !height:num.
        !summary:C.
          (balanced
             (AvlSplitNode
               left_tree datum right_tree height summary) <=>
           (&height:int) =
             real_height
               (AvlSplitNode
                 left_tree datum right_tree height summary) /\
           summary =
             agg measure_closure
               (seq_model
                 (AvlSplitNode
                   left_tree datum right_tree height summary)) /\
           (--(&balancing:int) <=
              real_height right_tree - real_height left_tree /\
            real_height right_tree - real_height left_tree <=
              (&balancing:int)) /\
           balanced left_tree /\ balanced right_tree)) /\
       (!self:B.
          balanced (repr self) /\
          seq self = seq_model (repr self) /\
          hgt self = real_height (repr self)) /\
       (!left right:B.
          repr left = repr right /\ m1 left = m1 right
          ==> left = right) /\
       0 < balancing /\
       (!selector:D.
          selection_possible selector []
          ==> selected selector empty_split)) in
    background
    ==> selection_possible s (seq t3)
    ==> view_fact
    ==> conclusion`;;

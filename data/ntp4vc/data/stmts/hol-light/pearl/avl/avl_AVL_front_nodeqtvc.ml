(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/avl_AVL_front_nodeqtvc: an AVL front-node verification condition
  relating a view decomposition to height growth and preservation of the
  initial sequence element. This file contains no proof.
*)

let avl_front_node_tree_INDUCT,avl_front_node_tree_RECURSION = define_type
  "avl_front_node_tree =
       AvlFrontNodeEmpty
     | AvlFrontNodeNode avl_front_node_tree A avl_front_node_tree num B";;

let statement =
 `!zero:C.
  !op:C->C->C.
  !agg:(A->C)->A list->C.
  !measure:A->C.
  !balancing:num.
  !measure_closure:A->C.
  !seq_model:(A,C)avl_front_node_tree->A list.
  !real_height:(A,C)avl_front_node_tree->int.
  !balanced:(A,C)avl_front_node_tree->bool.
  !repr:B->(A,C)avl_front_node_tree.
  !m1:B->A list#int.
  !o1:(B#A#B#num#C)option.
  !l:B.
  !d:A.
    let node_model =
      \(left:A list) (datum:A) (right:A list).
        APPEND left (CONS datum right) in
    let seq = \x:B. FST (m1 x) in
    let hgt = \x:B. SND (m1 x) in
    let payload =
      \view:(B#A#B#num#C)option. @p. view = SOME p in
    let left =
      \((left:B),(datum:A),(right:B),(height:num),(summary:C)).
        left in
    let datum =
      \((left:B),(datum:A),(right:B),(height:num),(summary:C)).
        datum in
    let right =
      \((left:B),(datum:A),(right:B),(height:num),(summary:C)).
        right in
    let stored_height =
      \((left:B),(datum:A),(right:B),(height:num),(summary:C)).
        height in
    let summary =
      \((left:B),(datum:A),(right:B),(height:num),(summary:C)).
        summary in
    let fact0 =
      if o1 = NONE then
        hgt l = (&0:int) /\ seq l = []
      else
        let p = payload o1 in
        let l1 = left p in
        let d2 = datum p in
        let r = right p in
        let h = stored_height p in
        let s = summary p in
        seq l = node_model (seq l1) d2 (seq r) /\
        s = agg measure_closure (seq l) /\
        let hl = hgt l1 in
        let hr = hgt r in
        (--(&balancing:int) <= hl - hr /\
         hl - hr <= (&balancing:int)) /\
        hgt l = (&h:int) /\
        (&h:int) =
          (&1:int) + (if hl < hr then hr else hl) in
    let background = (
      (!a b c:C. op a (op b c) = op (op a b) c) /\
      (!x:C. op x zero = x /\ x = op zero x) /\
      (!f:A->C. agg f [] = zero) /\
      (!s:A list. !f:A->C.
         (&(LENGTH s):int) = (&1:int)
         ==> agg f s = f (EL 0 s)) /\
      (!f:A->C. !s1 s2:A list.
         agg f (APPEND s1 s2) = op (agg f s1) (agg f s2)) /\
      (!y:A. measure_closure y = measure y) /\
      seq_model AvlFrontNodeEmpty = [] /\
      (!left1:(A,C)avl_front_node_tree.
       !datum1:A.
       !right1:(A,C)avl_front_node_tree.
       !height1:num.
       !summary1:C.
         seq_model
           (AvlFrontNodeNode left1 datum1 right1 height1 summary1) =
         node_model (seq_model left1) datum1 (seq_model right1)) /\
      real_height AvlFrontNodeEmpty = (&0:int) /\
      (!left1:(A,C)avl_front_node_tree.
       !datum1:A.
       !right1:(A,C)avl_front_node_tree.
       !height1:num.
       !summary1:C.
         real_height
           (AvlFrontNodeNode left1 datum1 right1 height1 summary1) =
         (&1:int) +
         (if real_height left1 < real_height right1
          then real_height right1 else real_height left1)) /\
      balanced AvlFrontNodeEmpty /\
      (!left1:(A,C)avl_front_node_tree.
       !datum1:A.
       !right1:(A,C)avl_front_node_tree.
       !height1:num.
       !summary1:C.
         (balanced
            (AvlFrontNodeNode
              left1 datum1 right1 height1 summary1) <=>
          (&height1:int) =
            real_height
              (AvlFrontNodeNode
                left1 datum1 right1 height1 summary1) /\
          summary1 =
            agg measure_closure
              (seq_model
                (AvlFrontNodeNode
                  left1 datum1 right1 height1 summary1)) /\
          (--(&balancing:int) <=
             real_height right1 - real_height left1 /\
           real_height right1 - real_height left1 <=
             (&balancing:int)) /\
          balanced left1 /\ balanced right1)) /\
      (!self:B.
         balanced (repr self) /\
         seq self = seq_model (repr self) /\
         hgt self = real_height (repr self)) /\
      (!a b:B.
         repr a = repr b /\ m1 a = m1 b ==> a = b) /\
      0 < balancing) in
    background
    ==> fact0
    ==> (if o1 = NONE then
           T
         else
           let p = payload o1 in
           (&0:int) <= hgt l /\ hgt (left p) < hgt l) /\
        (!result:A.
           (if o1 = NONE then
              result = d
            else
              let p = payload o1 in
              result =
                EL 0 (APPEND (seq (left p)) [datum p]))
           ==> result = EL 0 (APPEND (seq l) [d]))`;;

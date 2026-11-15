(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/avl_AVL_decompose_front_nodeqtvc: an AVL front decomposition
  verification condition for sequence splitting, balance bounds, and bounded
  cached-height change. This file contains no proof.
*)

let avl_decompose_front_tree_INDUCT,avl_decompose_front_tree_RECURSION =
  define_type
    "avl_decompose_front_tree =
         AvlDecomposeFrontEmpty
       | AvlDecomposeFrontNode
           avl_decompose_front_tree A avl_decompose_front_tree num C";;

let statement =
 `!zero:C.
  !op:C->C->C.
  !agg:(A->C)->A list->C.
  !measure:A->C.
  !balancing:num.
  !measure_closure:A->C.
  !seq_model:(A,C)avl_decompose_front_tree->A list.
  !real_height:(A,C)avl_decompose_front_tree->int.
  !balanced:(A,C)avl_decompose_front_tree->bool.
  !repr:B->(A,C)avl_decompose_front_tree.
  !m1:B->A list#int.
  !l r:B.
  !o1:(B#A#B#num#C)option.
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
    let within =
      \(left:B) (right:B).
        --(&balancing:int) <= hgt left - hgt right /\
        hgt left - hgt right <= (&balancing:int) in
    let expected_height =
      \(left:B) (right:B).
        (&1:int) +
        (if hgt left < hgt right then hgt right else hgt left) in
    let height_close =
      \(expected:int) (actual:int).
        (&0:int) <= expected - actual /\
        expected - actual <= (&1:int) in
    let view_fact =
      if o1 = NONE then
        hgt l = (&0:int) /\ seq l = []
      else
        let p = payload o1 in
        seq l =
          node_model (seq (left p)) (datum p) (seq (right p)) /\
        summary p = agg measure_closure (seq l) /\
        within (left p) (right p) /\
        hgt l = (&(stored_height p):int) /\
        (&(stored_height p):int) =
          expected_height (left p) (right p) in
    let node_case =
      if o1 = NONE then
        T
      else
        let p = payload o1 in
        (((&0:int) <= hgt l /\ hgt (left p) < hgt l) /\
         within (left p) (right p)) /\
        (!d3:A.
         !left1:B.
           node_model (seq (left p)) (datum p) (seq (right p)) =
             CONS d3 (seq left1) /\
           height_close
             (expected_height (left p) (right p))
             (hgt left1)
           ==> --(&balancing:int) - (&1:int) <=
                 hgt left1 - hgt r /\
               hgt left1 - hgt r <=
                 (&balancing:int) + (&1:int)) in
    let result_case =
      !d2:A.
      !res:B.
        (if o1 = NONE then
           d2 = d /\ res = r
         else
           let p = payload o1 in
           ?res1:B.
             (node_model
                (seq (left p)) (datum p) (seq (right p)) =
                  CONS d2 (seq res1) /\
              height_close
                (expected_height (left p) (right p))
                (hgt res1)) /\
             seq res = node_model (seq res1) d (seq r) /\
             height_close (expected_height res1 r) (hgt res) /\
             (within res1 r
              ==> expected_height res1 r = hgt res))
        ==> node_model (seq l) d (seq r) =
              CONS d2 (seq res) /\
            height_close (expected_height l r) (hgt res) in
    let background =
      ((!a b c:C. op a (op b c) = op (op a b) c) /\
      (!x:C. op x zero = x /\ x = op zero x) /\
      (!f:A->C. agg f [] = zero) /\
      (!s:A list.
       !f:A->C.
         (&(LENGTH s):int) = (&1:int)
         ==> agg f s = f (EL 0 s)) /\
      (!f:A->C.
       !s1 s2:A list.
         agg f (APPEND s1 s2) = op (agg f s1) (agg f s2)) /\
      (!y:A. measure_closure y = measure y) /\
      seq_model AvlDecomposeFrontEmpty = [] /\
      (!left1:(A,C)avl_decompose_front_tree.
       !datum1:A.
       !right1:(A,C)avl_decompose_front_tree.
       !height1:num.
       !summary1:C.
         seq_model
           (AvlDecomposeFrontNode
             left1 datum1 right1 height1 summary1) =
         node_model (seq_model left1) datum1 (seq_model right1)) /\
      real_height AvlDecomposeFrontEmpty = (&0:int) /\
      (!left1:(A,C)avl_decompose_front_tree.
       !datum1:A.
       !right1:(A,C)avl_decompose_front_tree.
       !height1:num.
       !summary1:C.
         real_height
           (AvlDecomposeFrontNode
             left1 datum1 right1 height1 summary1) =
         (&1:int) +
         (if real_height left1 < real_height right1
          then real_height right1 else real_height left1)) /\
      balanced AvlDecomposeFrontEmpty /\
      (!left1:(A,C)avl_decompose_front_tree.
       !datum1:A.
       !right1:(A,C)avl_decompose_front_tree.
       !height1:num.
       !summary1:C.
         (balanced
            (AvlDecomposeFrontNode
              left1 datum1 right1 height1 summary1) <=>
          (&height1:int) =
            real_height
              (AvlDecomposeFrontNode
                left1 datum1 right1 height1 summary1) /\
          summary1 =
            agg measure_closure
              (seq_model
                (AvlDecomposeFrontNode
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
    ==> --(&balancing:int) <= hgt l - hgt r
    ==> hgt l - hgt r <= (&balancing:int)
    ==> view_fact
    ==> node_case /\ result_case`;;

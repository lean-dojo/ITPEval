(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/avl_AVL_decompose_back_nodeqtvc: an AVL back decomposition
  verification condition for sequence splitting, balance bounds, and bounded
  cached-height change. This file contains no proof.
*)

let avl_decompose_back_tree_INDUCT,avl_decompose_back_tree_RECURSION =
  define_type
    "avl_decompose_back_tree =
         AvlDecomposeBackEmpty
       | AvlDecomposeBackNode
           avl_decompose_back_tree A avl_decompose_back_tree num C";;

let statement =
 `!zero:C.
  !op:C->C->C.
  !agg:(A->C)->A list->C.
  !measure:A->C.
  !balancing:num.
  !measure_closure:A->C.
  !seq_model:(A,C)avl_decompose_back_tree->A list.
  !real_height:(A,C)avl_decompose_back_tree->int.
  !balanced:(A,C)avl_decompose_back_tree->bool.
  !repr:B->(A,C)avl_decompose_back_tree.
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
        hgt r = (&0:int) /\ seq r = []
      else
        let p = payload o1 in
        seq r =
          node_model (seq (left p)) (datum p) (seq (right p)) /\
        summary p = agg measure_closure (seq r) /\
        within (left p) (right p) /\
        hgt r = (&(stored_height p):int) /\
        (&(stored_height p):int) =
          expected_height (left p) (right p) in
    let node_case =
      if o1 = NONE then
        T
      else
        let p = payload o1 in
        (((&0:int) <= hgt r /\ hgt (right p) < hgt r) /\
         within (left p) (right p)) /\
        (!right1:B.
         !d3:A.
           node_model (seq (left p)) (datum p) (seq (right p)) =
             APPEND (seq right1) [d3] /\
           height_close
             (expected_height (left p) (right p))
             (hgt right1)
           ==> --(&balancing:int) - (&1:int) <=
                 hgt l - hgt right1 /\
               hgt l - hgt right1 <=
                 (&balancing:int) + (&1:int)) in
    let result_case =
      !res:B.
      !d2:A.
        (if o1 = NONE then
           res = l /\ d2 = d
         else
           let p = payload o1 in
           ?res1:B.
             (node_model
                (seq (left p)) (datum p) (seq (right p)) =
                  APPEND (seq res1) [d2] /\
              height_close
                (expected_height (left p) (right p))
                (hgt res1)) /\
             seq res = node_model (seq l) d (seq res1) /\
             height_close (expected_height l res1) (hgt res) /\
             (within l res1
              ==> expected_height l res1 = hgt res))
        ==> node_model (seq l) d (seq r) =
              APPEND (seq res) [d2] /\
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
      seq_model AvlDecomposeBackEmpty = [] /\
      (!left1:(A,C)avl_decompose_back_tree.
       !datum1:A.
       !right1:(A,C)avl_decompose_back_tree.
       !height1:num.
       !summary1:C.
         seq_model
           (AvlDecomposeBackNode
             left1 datum1 right1 height1 summary1) =
         node_model (seq_model left1) datum1 (seq_model right1)) /\
      real_height AvlDecomposeBackEmpty = (&0:int) /\
      (!left1:(A,C)avl_decompose_back_tree.
       !datum1:A.
       !right1:(A,C)avl_decompose_back_tree.
       !height1:num.
       !summary1:C.
         real_height
           (AvlDecomposeBackNode
             left1 datum1 right1 height1 summary1) =
         (&1:int) +
         (if real_height left1 < real_height right1
          then real_height right1 else real_height left1)) /\
      balanced AvlDecomposeBackEmpty /\
      (!left1:(A,C)avl_decompose_back_tree.
       !datum1:A.
       !right1:(A,C)avl_decompose_back_tree.
       !height1:num.
       !summary1:C.
         (balanced
            (AvlDecomposeBackNode
              left1 datum1 right1 height1 summary1) <=>
          (&height1:int) =
            real_height
              (AvlDecomposeBackNode
                left1 datum1 right1 height1 summary1) /\
          summary1 =
            agg measure_closure
              (seq_model
                (AvlDecomposeBackNode
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

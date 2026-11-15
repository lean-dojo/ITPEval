(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/avl_AVL_fuseqtvc: an AVL-tree fuse verification condition for
  concatenated sequence preservation and bounded cached-height change under
  view-based decomposition of the two input trees. This file contains no proof.
*)

let avl_fuse_tree_INDUCT,avl_fuse_tree_RECURSION = define_type
  "avl_fuse_tree =
       AvlFuseEmpty
     | AvlFuseNode avl_fuse_tree A avl_fuse_tree num C";;

let statement =
 `!zero:C.
  !op:C->C->C.
  !agg:(A->C)->A list->C.
  !measure:A->C.
  !balancing:num.
  !measure_closure:A->C.
  !seq_model:(A,C)avl_fuse_tree->A list.
  !real_height:(A,C)avl_fuse_tree->int.
  !balanced:(A,C)avl_fuse_tree->bool.
  !repr:B->(A,C)avl_fuse_tree.
  !m1:B->A list#int.
  !l r:B.
  !o1:(B#A#B#num#C)option.
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
    let widened =
      \(left:B) (right:B).
        --(&balancing:int) - (&1:int) <= hgt left - hgt right /\
        hgt left - hgt right <= (&balancing:int) + (&1:int) in
    let expected_height =
      \(left:B) (right:B).
        (&1:int) +
        (if hgt left < hgt right then hgt right else hgt left) in
    let height_close =
      \(expected:int) (actual:int).
        (&0:int) <= expected - actual /\
        expected - actual <= (&1:int) in
    let view_fact =
      \(subject:B) (view:(B#A#B#num#C)option).
        if view = NONE then
          hgt subject = (&0:int) /\ seq subject = []
        else
          let p = payload view in
          let left1 = left p in
          let datum1 = datum p in
          let right1 = right p in
          let height1 = stored_height p in
          let summary1 = summary p in
          seq subject =
            node_model (seq left1) datum1 (seq right1) /\
          summary1 = agg measure_closure (seq subject) /\
          within left1 right1 /\
          hgt subject = (&height1:int) /\
          (&height1:int) = expected_height left1 right1 in
    let operational =
      if o1 = NONE then
        T
      else
        !o2:(B#A#B#num#C)option.
          view_fact r o2
          ==> if o2 = NONE then
                T
              else
                let p = payload o2 in
                let rl = left p in
                let rd = datum p in
                let rr = right p in
                within rl rr /\
                (!d0:A.
                 !r':B.
                   node_model (seq rl) rd (seq rr) =
                     CONS d0 (seq r') /\
                   height_close
                     (expected_height rl rr) (hgt r')
                   ==> widened l r') in
    let construction =
      \(result:B).
        if o1 = NONE then
          result = r
        else
          ?o2:(B#A#B#num#C)option.
            view_fact r o2 /\
            (if o2 = NONE then
               result = l
             else
               let p = payload o2 in
               let rl = left p in
               let rd = datum p in
               let rr = right p in
               ?d2:A.
               ?res:B.
                 (node_model (seq rl) rd (seq rr) =
                    CONS d2 (seq res) /\
                  height_close
                    (expected_height rl rr) (hgt res)) /\
                 seq result =
                   node_model (seq l) d2 (seq res) /\
                 height_close
                   (expected_height l res) (hgt result) /\
                 (within l res
                  ==> expected_height l res = hgt result)) in
    let final_result =
      \(result:B).
        seq result = APPEND (seq l) (seq r) /\
        expected_height l r - hgt result <= (&1:int) /\
        (&0:int) <= expected_height l r - hgt result in
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
       seq_model AvlFuseEmpty = [] /\
       (!left1:(A,C)avl_fuse_tree.
        !datum1:A.
        !right1:(A,C)avl_fuse_tree.
        !height1:num.
        !summary1:C.
          seq_model
            (AvlFuseNode left1 datum1 right1 height1 summary1) =
          node_model
            (seq_model left1) datum1 (seq_model right1)) /\
       real_height AvlFuseEmpty = (&0:int) /\
       (!left1:(A,C)avl_fuse_tree.
        !datum1:A.
        !right1:(A,C)avl_fuse_tree.
        !height1:num.
        !summary1:C.
          real_height
            (AvlFuseNode left1 datum1 right1 height1 summary1) =
          (&1:int) +
          (if real_height left1 < real_height right1
           then real_height right1 else real_height left1)) /\
       balanced AvlFuseEmpty /\
       (!left1:(A,C)avl_fuse_tree.
        !datum1:A.
        !right1:(A,C)avl_fuse_tree.
        !height1:num.
        !summary1:C.
          (balanced
             (AvlFuseNode left1 datum1 right1 height1 summary1) <=>
           (&height1:int) =
             real_height
               (AvlFuseNode
                 left1 datum1 right1 height1 summary1) /\
           summary1 =
             agg measure_closure
               (seq_model
                 (AvlFuseNode
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
    ==> view_fact l o1
    ==> operational /\
        (!result:B.
           construction result
           ==> final_result result)`;;

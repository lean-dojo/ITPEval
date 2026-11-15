(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/avl_AVL_joinqtvc: an AVL-tree join verification condition for
  sequence preservation and bounded cached-height change across recursive
  view-based rebalancing. This file contains no proof.
*)

let avl_join_tree_INDUCT,avl_join_tree_RECURSION = define_type
  "avl_join_tree =
       AvlJoinEmpty
     | AvlJoinNode avl_join_tree A avl_join_tree num C";;

let statement =
 `!zero:C.
  !op:C->C->C.
  !agg:(A->C)->A list->C.
  !measure:A->C.
  !balancing:num.
  !measure_closure:A->C.
  !seq_model:(A,C)avl_join_tree->A list.
  !real_height:(A,C)avl_join_tree->int.
  !balanced:(A,C)avl_join_tree->bool.
  !repr:B->(A,C)avl_join_tree.
  !m1:B->A list#int.
  !o1:(B#A#B#num#C)option.
  !l r:B.
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
    let height_distance =
      \(left:B) (right:B).
        if hgt right < hgt left
        then hgt left - hgt right
        else hgt right - hgt left in
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
    let built_close =
      \(result:B) (left1:B) (datum1:A) (right1:B).
        seq result =
          node_model (seq left1) datum1 (seq right1) /\
        height_close (expected_height left1 right1) (hgt result) in
    let built_balanced =
      \(result:B) (left1:B) (datum1:A) (right1:B).
        seq result =
          node_model (seq left1) datum1 (seq right1) /\
        height_close (expected_height left1 right1) (hgt result) /\
        (within left1 right1
         ==> expected_height left1 right1 = hgt result) in
    let built_exact =
      \(result:B) (left1:B) (datum1:A) (right1:B).
        seq result =
          node_model (seq left1) datum1 (seq right1) /\
        hgt result = expected_height left1 right1 in
    let operational =
      if o1 = NONE then
        T
      else
        let p1 = payload o1 in
        let ll = left p1 in
        let lr = right p1 in
        let lh = stored_height p1 in
        !o2:(B#A#B#num#C)option.
          view_fact r o2
          ==> if o2 = NONE then
                T
              else
                let p2 = payload o2 in
                let rl = left p2 in
                let rr = right p2 in
                let rh = stored_height p2 in
                !o3:int.
                  o3 = --(&rh:int)
                  ==> (o3 <= (&lh:int) - (&rh:int) /\
                       (&lh:int) - (&rh:int) <= (&lh:int)) /\
                      (!df:int.
                         df = (&lh:int) - (&rh:int)
                         ==> if (&balancing:int) < df then
                               ((&0:int) <= height_distance l r /\
                                height_distance lr r <
                                  height_distance l r) /\
                               (!o4:B.
                                  built_close o4 lr d r
                                  ==> widened ll o4)
                             else
                               !o4:int.
                                 o4 = --(&balancing:int)
                                 ==> if df < o4 then
                                       ((&0:int) <=
                                          height_distance l r /\
                                        height_distance l rl <
                                          height_distance l r) /\
                                       (!o5:B.
                                          built_close o5 l d rl
                                          ==> widened o5 rr)
                                     else
                                       within l r) in
    let construction =
      \(result:B).
        if o1 = NONE then
          seq result = CONS d (seq r) /\
          hgt result - hgt r <= (&1:int) /\
          (&0:int) <= hgt result - hgt r
        else
          let p1 = payload o1 in
          let ll = left p1 in
          let ld = datum p1 in
          let lr = right p1 in
          let lh = stored_height p1 in
          ?o2:(B#A#B#num#C)option.
            view_fact r o2 /\
            (if o2 = NONE then
               seq result = APPEND (seq l) [d] /\
               hgt result - hgt l <= (&1:int) /\
               (&0:int) <= hgt result - hgt l
             else
               let p2 = payload o2 in
               let rl = left p2 in
               let rd = datum p2 in
               let rr = right p2 in
               let rh = stored_height p2 in
               ?o3:int.
                 o3 = --(&rh:int) /\
                 ?df:int.
                   df = (&lh:int) - (&rh:int) /\
                   (if (&balancing:int) < df then
                      ?o4:B.
                        built_close o4 lr d r /\
                        built_balanced result ll ld o4
                    else
                      ?o4:int.
                        o4 = --(&balancing:int) /\
                        (if df < o4 then
                           ?o5:B.
                             built_close o5 l d rl /\
                             built_balanced result o5 rd rr
                         else
                           built_exact result l d r))) in
    let final_result =
      \(result:B).
        seq result = node_model (seq l) d (seq r) /\
        height_close (expected_height l r) (hgt result) in
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
       seq_model AvlJoinEmpty = [] /\
       (!left1:(A,C)avl_join_tree.
        !datum1:A.
        !right1:(A,C)avl_join_tree.
        !height1:num.
        !summary1:C.
          seq_model
            (AvlJoinNode left1 datum1 right1 height1 summary1) =
          node_model
            (seq_model left1) datum1 (seq_model right1)) /\
       real_height AvlJoinEmpty = (&0:int) /\
       (!left1:(A,C)avl_join_tree.
        !datum1:A.
        !right1:(A,C)avl_join_tree.
        !height1:num.
        !summary1:C.
          real_height
            (AvlJoinNode left1 datum1 right1 height1 summary1) =
          (&1:int) +
          (if real_height left1 < real_height right1
           then real_height right1 else real_height left1)) /\
       balanced AvlJoinEmpty /\
       (!left1:(A,C)avl_join_tree.
        !datum1:A.
        !right1:(A,C)avl_join_tree.
        !height1:num.
        !summary1:C.
          (balanced
             (AvlJoinNode left1 datum1 right1 height1 summary1) <=>
           (&height1:int) =
             real_height
               (AvlJoinNode
                 left1 datum1 right1 height1 summary1) /\
           summary1 =
             agg measure_closure
               (seq_model
                 (AvlJoinNode
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
    ==> view_fact l o1
    ==> operational /\
        (!result:B.
           construction result
           ==> final_result result)`;;

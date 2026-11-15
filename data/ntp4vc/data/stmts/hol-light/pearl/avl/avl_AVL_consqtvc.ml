(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/avl_AVL_consqtvc: an AVL-tree cons verification condition relating
  a view decomposition to sequence preservation, balance bounds, and bounded
  cached-height growth. This file contains no proof.
*)

let avl_cons_tree_INDUCT,avl_cons_tree_RECURSION = define_type
  "avl_cons_tree =
       AvlConsEmpty
     | AvlConsNode avl_cons_tree A avl_cons_tree num B";;

let statement =
 `!zero:C.
  !op:C->C->C.
  !agg:(A->C)->A list->C.
  !measure:A->C.
  !balancing:num.
  !measure_closure:A->C.
  !seq_model:(A,C)avl_cons_tree->A list.
  !real_height:(A,C)avl_cons_tree->int.
  !balanced:(A,C)avl_cons_tree->bool.
  !repr:B->(A,C)avl_cons_tree.
  !m1:B->A list#int.
  !o1:(B#A#B#num#C)option.
  !t3:B.
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
        hgt t3 = (&0:int) /\ seq t3 = []
      else
        let p = payload o1 in
        let l = left p in
        let d2 = datum p in
        let r = right p in
        let h = stored_height p in
        let s = summary p in
        seq t3 = node_model (seq l) d2 (seq r) /\
        s = agg measure_closure (seq t3) /\
        let hl = hgt l in
        let hr = hgt r in
        (--(&balancing:int) <= hl - hr /\
         hl - hr <= (&balancing:int)) /\
        hgt t3 = (&h:int) /\
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
      seq_model AvlConsEmpty = [] /\
      (!left1:(A,C)avl_cons_tree.
       !datum1:A.
       !right1:(A,C)avl_cons_tree.
       !height1:num.
       !summary1:C.
         seq_model
           (AvlConsNode left1 datum1 right1 height1 summary1) =
         node_model (seq_model left1) datum1 (seq_model right1)) /\
      real_height AvlConsEmpty = (&0:int) /\
      (!left1:(A,C)avl_cons_tree.
       !datum1:A.
       !right1:(A,C)avl_cons_tree.
       !height1:num.
       !summary1:C.
         real_height
           (AvlConsNode left1 datum1 right1 height1 summary1) =
         (&1:int) +
         (if real_height left1 < real_height right1
          then real_height right1 else real_height left1)) /\
      balanced AvlConsEmpty /\
      (!left1:(A,C)avl_cons_tree.
       !datum1:A.
       !right1:(A,C)avl_cons_tree.
       !height1:num.
       !summary1:C.
         (balanced
            (AvlConsNode left1 datum1 right1 height1 summary1) <=>
          (&height1:int) =
            real_height
              (AvlConsNode
                left1 datum1 right1 height1 summary1) /\
          summary1 =
            agg measure_closure
              (seq_model
                (AvlConsNode
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
           let l = left p in
           let r = right p in
           ((&0:int) <= hgt t3 /\ hgt l < hgt t3) /\
           (!o2:B.
              seq o2 = CONS d (seq l) /\
              hgt o2 - hgt l <= (&1:int) /\
              (&0:int) <= hgt o2 - hgt l
              ==> --(&balancing:int) - (&1:int) <=
                    hgt o2 - hgt r /\
                  hgt o2 - hgt r <=
                    (&balancing:int) + (&1:int))) /\
        (!result:B.
           (if o1 = NONE then
              seq result = [d] /\ hgt result = (&1:int)
            else
              let p = payload o1 in
              let l = left p in
              let d2 = datum p in
              let r = right p in
              ?o2:B.
                (seq o2 = CONS d (seq l) /\
                 hgt o2 - hgt l <= (&1:int) /\
                 (&0:int) <= hgt o2 - hgt l) /\
                seq result = node_model (seq o2) d2 (seq r) /\
                let hl = hgt o2 in
                let hr = hgt r in
                let he =
                  (&1:int) + (if hl < hr then hr else hl) in
                let hres = hgt result in
                ((&0:int) <= he - hres /\
                 he - hres <= (&1:int)) /\
                ((--(&balancing:int) <= hl - hr /\
                  hl - hr <= (&balancing:int))
                 ==> he = hres))
           ==> seq result = CONS d (seq t3) /\
               hgt result - hgt t3 <= (&1:int) /\
               (&0:int) <= hgt result - hgt t3)`;;

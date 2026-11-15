(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/avl_AVL_back_nodeqtvc: an AVL back-node verification condition
  relating a view decomposition to height growth and preservation of the
  final sequence element. This file contains no proof.
*)

let avl_back_node_tree_INDUCT,avl_back_node_tree_RECURSION = define_type
  "avl_back_node_tree =
       AvlBackNodeEmpty
     | AvlBackNodeNode avl_back_node_tree A avl_back_node_tree num C";;

let statement =
 `let node_model =
    \(l:A list) (d:A) (r:A list). APPEND l (CONS d r) in
  let payload =
    \v:(B#A#B#num#C)option. @p. v = SOME p in
  let left =
    \((l:B),(d2:A),(r1:B),(h:num),(s:C)). l in
  let datum =
    \((l:B),(d2:A),(r1:B),(h:num),(s:C)). d2 in
  let right =
    \((l:B),(d2:A),(r1:B),(h:num),(s:C)). r1 in
  let stored_height =
    \((l:B),(d2:A),(r1:B),(h:num),(s:C)). h in
  let summary =
    \((l:B),(d2:A),(r1:B),(h:num),(s:C)). s in
  !zero:C.
  !op:C->C->C.
  !agg:(A->C)->A list->C.
  !measure:A->C.
  !seq_model:(A,C)avl_back_node_tree->A list.
  !real_height:(A,C)avl_back_node_tree->int.
  !balanced:(A,C)avl_back_node_tree->bool.
  !repr:B->(A,C)avl_back_node_tree.
  !measure_closure:A->C.
  !m1:B->A list#int.
  !o1:(B#A#B#num#C)option.
  !r:B.
  !d:A.
  !balancing:num.
    let seq = \x:B. FST (m1 x) in
    let hgt = \x:B. SND (m1 x) in
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
       seq_model AvlBackNodeEmpty = [] /\
       (!left1:(A,C)avl_back_node_tree.
        !datum1:A.
        !right1:(A,C)avl_back_node_tree.
        !height1:num.
        !summary1:C.
          seq_model
            (AvlBackNodeNode
              left1 datum1 right1 height1 summary1) =
          node_model
            (seq_model left1) datum1 (seq_model right1)) /\
       real_height AvlBackNodeEmpty = (&0:int) /\
       (!left1:(A,C)avl_back_node_tree.
        !datum1:A.
        !right1:(A,C)avl_back_node_tree.
        !height1:num.
        !summary1:C.
          real_height
            (AvlBackNodeNode
              left1 datum1 right1 height1 summary1) =
          (&1:int) +
          (if real_height left1 < real_height right1
           then real_height right1 else real_height left1)) /\
       balanced AvlBackNodeEmpty /\
       (!left1:(A,C)avl_back_node_tree.
        !datum1:A.
        !right1:(A,C)avl_back_node_tree.
        !height1:num.
        !summary1:C.
          (balanced
             (AvlBackNodeNode
               left1 datum1 right1 height1 summary1) <=>
           (&height1:int) =
             real_height
               (AvlBackNodeNode
                 left1 datum1 right1 height1 summary1) /\
           summary1 =
             agg measure_closure
               (seq_model
                 (AvlBackNodeNode
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
    let fact0 =
      if o1 = NONE then
        hgt r = (&0:int) /\ seq r = []
      else
        let p = payload o1 in
        let l = left p in
        let d2 = datum p in
        let r1 = right p in
        let h = stored_height p in
        let s = summary p in
        seq r = node_model (seq l) d2 (seq r1) /\
        s = agg measure_closure (seq r) /\
        let hl = hgt l in
        let hr = hgt r1 in
        (--(&balancing:int) <= hl - hr /\
         hl - hr <= (&balancing:int)) /\
        hgt r = (&h:int) /\
        (&h:int) = (&1:int) + (if hl < hr then hr else hl) in
    background
    ==> fact0
    ==> (if o1 = NONE then
           T
         else
           let p = payload o1 in
           (&0:int) <= hgt r /\ hgt (right p) < hgt r) /\
        (!result:A.
           (if o1 = NONE then
              result = d
            else
              let p = payload o1 in
              result =
              EL (LENGTH (seq (right p)))
                 (CONS (datum p) (seq (right p))))
           ==> result =
               EL (LENGTH (seq r)) (CONS d (seq r)))`;;

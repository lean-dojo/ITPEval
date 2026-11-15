(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/binomial_heap_BinomialHeap_extract_min_treeqtvc: a binomial-heap
  extract-min-tree verification condition preserving heap order, rank
  invariants, root minimality, and element multiplicities. This file contains
  no proof.
*)

let binomial_heap_tree_INDUCT,binomial_heap_tree_RECURSION = define_type
  "binomial_heap_tree =
     BinomialHeapTree A (binomial_heap_tree list) int";;

let statement =
 `!bh_le:A->A->bool.
  !bh_elem:A binomial_heap_tree->A.
  !bh_children:A binomial_heap_tree->(A binomial_heap_tree)list.
  !bh_rank:A binomial_heap_tree->int.
  !bh_le_roots:A->(A binomial_heap_tree)list->bool.
  !bh_heaps:(A binomial_heap_tree)list->bool.
  !bh_occ:A->(A binomial_heap_tree)list->int.
  !bh_has_order:int->(A binomial_heap_tree)list->bool.
  !bh_inv:int->(A binomial_heap_tree)list->bool.
  !h:(A binomial_heap_tree)list.
  !k:int.
    let binomial_tree =
      \t:A binomial_heap_tree.
        bh_rank t = (&(LENGTH (bh_children t)):int) /\
        bh_has_order (bh_rank t) (bh_children t) in
    let progress =
      ((?t:A binomial_heap_tree. h = [t]) \/
       (?t:A binomial_heap_tree.
        ?tl:(A binomial_heap_tree)list.
          h = CONS t tl /\
          ~(tl = []) /\
          bh_heaps tl /\
          bh_inv (bh_rank t + (&1:int)) tl /\
          ~(tl = []))) in
    let extraction_case =
      \(t:A binomial_heap_tree) (h':(A binomial_heap_tree)list).
        (?t1:A binomial_heap_tree.
           h = [t1] /\ t = t1 /\ h' = []) \/
        (?t1:A binomial_heap_tree.
         ?tl:(A binomial_heap_tree)list.
           h = CONS t1 tl /\
           ~(tl = []) /\
           (?t2:A binomial_heap_tree.
            ?h1:(A binomial_heap_tree)list.
              (bh_heaps [t2] /\
               bh_heaps h1 /\
               bh_inv (bh_rank t1 + (&1:int)) h1 /\
               bh_le_roots (bh_elem t2) tl /\
               binomial_tree t2 /\
               (!x:A.
                  bh_occ x tl = bh_occ x [t2] + bh_occ x h1)) /\
              (if bh_le (bh_elem t1) (bh_elem t2) then
                 t = t1 /\ h' = tl
               else
                 t = t2 /\ h' = CONS t1 h1))) in
    let background =
      ((!x:A. bh_le x x) /\
       (!x y z:A. bh_le x y /\ bh_le y z ==> bh_le x z) /\
       (!x y:A. bh_le x y \/ bh_le y x) /\
       (!e:A.
        !c:(A binomial_heap_tree)list.
        !r:int.
          bh_elem (BinomialHeapTree e c r) = e /\
          bh_children (BinomialHeapTree e c r) = c /\
          bh_rank (BinomialHeapTree e c r) = r) /\
       (!e:A. bh_le_roots e [] <=> T) /\
       (!e:A.
        !t:A binomial_heap_tree.
        !r:(A binomial_heap_tree)list.
          (bh_le_roots e (CONS t r) <=>
           bh_le e (bh_elem t) /\ bh_le_roots e r)) /\
       (bh_heaps [] <=> T) /\
       (!e:A.
        !c:(A binomial_heap_tree)list.
        !rnk:int.
        !r:(A binomial_heap_tree)list.
          (bh_heaps (CONS (BinomialHeapTree e c rnk) r) <=>
           bh_le_roots e c /\ bh_heaps c /\ bh_heaps r)) /\
       (!x:A. bh_occ x [] = (&0:int)) /\
       (!x y:A.
        !c:(A binomial_heap_tree)list.
        !rnk:int.
        !r:(A binomial_heap_tree)list.
          bh_occ x (CONS (BinomialHeapTree y c rnk) r) =
          (if x = y then (&1:int) else (&0:int)) +
          bh_occ x c + bh_occ x r) /\
       (!m:int. bh_has_order m [] <=> m = (&0:int)) /\
       (!m:int.
        !x:A.
        !c:(A binomial_heap_tree)list.
        !rnk:int.
        !r:(A binomial_heap_tree)list.
          (bh_has_order m (CONS (BinomialHeapTree x c rnk) r) <=>
           rnk = m - (&1:int) /\
           bh_has_order (m - (&1:int)) c /\
           bh_has_order (m - (&1:int)) r)) /\
       (!m:int. bh_inv m [] <=> T) /\
       (!m:int.
        !t:A binomial_heap_tree.
        !r:(A binomial_heap_tree)list.
          (bh_inv m (CONS t r) <=>
           m <= bh_rank t /\
           binomial_tree t /\
           bh_inv (bh_rank t + (&1:int)) r))) in
    background
    ==> bh_heaps h
    ==> bh_inv k h
    ==> ~(h = [])
    ==> progress /\
        (!t:A binomial_heap_tree.
         !h':(A binomial_heap_tree)list.
           extraction_case t h'
           ==>
           bh_heaps [t] /\
           bh_heaps h' /\
           bh_inv k h' /\
           bh_le_roots (bh_elem t) h /\
           binomial_tree t /\
           (!x:A.
              bh_occ x h = bh_occ x [t] + bh_occ x h'))`;;

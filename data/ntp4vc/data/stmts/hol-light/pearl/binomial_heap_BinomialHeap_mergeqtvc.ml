(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/binomial_heap_BinomialHeap_mergeqtvc: a binomial-heap merge
  verification condition preserving heap order, binomial-rank invariants,
  and element multiplicities across all rank-comparison branches. This file
  contains no proof.
*)

let ntp4vc_binomial_merge_tree_INDUCT,ntp4vc_binomial_merge_tree_RECURSION =
  define_type
    "ntp4vc_binomial_merge_tree =
       NTP4VCBinomialMergeTree
         A (ntp4vc_binomial_merge_tree list) int";;

let statement =
 `!le:A->A->bool.
  !elem:A ntp4vc_binomial_merge_tree->A.
  !children:A ntp4vc_binomial_merge_tree->
    (A ntp4vc_binomial_merge_tree)list.
  !rank:A ntp4vc_binomial_merge_tree->int.
  !le_roots:A->(A ntp4vc_binomial_merge_tree)list->bool.
  !heaps:(A ntp4vc_binomial_merge_tree)list->bool.
  !occ:A->(A ntp4vc_binomial_merge_tree)list->int.
  !has_order:int->(A ntp4vc_binomial_merge_tree)list->bool.
  !heap_inv:int->(A ntp4vc_binomial_merge_tree)list->bool.
  !h1:(A ntp4vc_binomial_merge_tree)list.
  !k:int.
  !h2:(A ntp4vc_binomial_merge_tree)list.
    let binomial_tree =
      \t:A ntp4vc_binomial_merge_tree.
        rank t = (&(LENGTH (children t)):int) /\
        has_order (rank t) (children t) in
    let link =
      \(t1:A ntp4vc_binomial_merge_tree)
       (t2:A ntp4vc_binomial_merge_tree).
        if le (elem t1) (elem t2) then
          NTP4VCBinomialMergeTree
            (elem t1) (CONS t2 (children t1)) (rank t1 + (&1:int))
        else
          NTP4VCBinomialMergeTree
            (elem t2) (CONS t1 (children t2)) (rank t2 + (&1:int)) in
    let tail_is =
      \(forest:(A ntp4vc_binomial_merge_tree)list)
       (tail:(A ntp4vc_binomial_merge_tree)list).
        ~(forest = []) /\ TL forest = tail in
    let merge_step =
      (h2 = [] \/
      (?x:A ntp4vc_binomial_merge_tree.
       ?x1:(A ntp4vc_binomial_merge_tree)list.
         h2 = CONS x x1 /\
         (h1 = [] \/
          (?x2:A ntp4vc_binomial_merge_tree.
           ?x3:(A ntp4vc_binomial_merge_tree)list.
             h1 = CONS x2 x3 /\
             (if rank x2 < rank x then
                let o1 = rank x2 + (&1:int) in
                  tail_is h1 x3 /\
                  heaps x3 /\
                  heap_inv o1 x3 /\
                  heaps h2 /\
                  heap_inv o1 h2
              else if rank x < rank x2 then
                let o1 = rank x + (&1:int) in
                  tail_is h2 x1 /\
                  heaps h1 /\
                  heap_inv o1 h1 /\
                  heaps x1 /\
                  heap_inv o1 x1
              else
                let o1 = rank x2 + (&1:int) in
                  ((tail_is h1 x3 \/
                    h1 = x3 /\ tail_is h2 x1) /\
                   heaps x3 /\
                   heap_inv o1 x3 /\
                   heaps x1 /\
                   heap_inv o1 x1) /\
                  (!o2:(A ntp4vc_binomial_merge_tree)list.
                     heaps o2 /\
                     heap_inv o1 o2 /\
                     (!x4:A.
                        occ x4 o2 = occ x4 x3 + occ x4 x1)
                     ==>
                     (let o3 = link x2 x in
                        heaps [o3] /\
                        binomial_tree o3 /\
                        heaps o2 /\
                        heap_inv (rank o3) o2))))))) in
    let result_case =
      \result:(A ntp4vc_binomial_merge_tree)list.
        (h2 = [] /\
         ((h1 = [] /\ result = h2) \/
          (?x2:A ntp4vc_binomial_merge_tree.
           ?x3:(A ntp4vc_binomial_merge_tree)list.
             h1 = CONS x2 x3 /\ result = h1))) \/
        (?x:A ntp4vc_binomial_merge_tree.
         ?x1:(A ntp4vc_binomial_merge_tree)list.
           h2 = CONS x x1 /\
           ((h1 = [] /\ result = h2) \/
            (?x2:A ntp4vc_binomial_merge_tree.
             ?x3:(A ntp4vc_binomial_merge_tree)list.
               h1 = CONS x2 x3 /\
               (if rank x2 < rank x then
                  ?o1:(A ntp4vc_binomial_merge_tree)list.
                    (heaps o1 /\
                     heap_inv (rank x2 + (&1:int)) o1 /\
                     (!x4:A.
                        occ x4 o1 = occ x4 x3 + occ x4 h2)) /\
                    result = CONS x2 o1
                else if rank x < rank x2 then
                  ?o1:(A ntp4vc_binomial_merge_tree)list.
                    (heaps o1 /\
                     heap_inv (rank x + (&1:int)) o1 /\
                     (!x4:A.
                        occ x4 o1 = occ x4 h1 + occ x4 x1)) /\
                    result = CONS x o1
                else
                  ?o1:(A ntp4vc_binomial_merge_tree)list.
                    (heaps o1 /\
                     heap_inv (rank x2 + (&1:int)) o1 /\
                     (!x4:A.
                        occ x4 o1 = occ x4 x3 + occ x4 x1)) /\
                    (let o2 = link x2 x in
                       heaps result /\
                       heap_inv (rank o2) result /\
                       (!x4:A.
                          occ x4 result = occ x4 [o2] + occ x4 o1)))))) in
    let background =
      ((!x:A. le x x) /\
       (!x y z:A. le x y /\ le y z ==> le x z) /\
       (!x y:A. le x y \/ le y x) /\
       (!e:A.
        !c:(A ntp4vc_binomial_merge_tree)list.
        !r:int.
          elem (NTP4VCBinomialMergeTree e c r) = e /\
          children (NTP4VCBinomialMergeTree e c r) = c /\
          rank (NTP4VCBinomialMergeTree e c r) = r) /\
       (!e:A. le_roots e [] <=> T) /\
       (!e:A.
        !t:A ntp4vc_binomial_merge_tree.
        !r:(A ntp4vc_binomial_merge_tree)list.
          (le_roots e (CONS t r) <=>
           le e (elem t) /\ le_roots e r)) /\
       (heaps [] <=> T) /\
       (!e:A.
        !c:(A ntp4vc_binomial_merge_tree)list.
        !rnk:int.
        !r:(A ntp4vc_binomial_merge_tree)list.
          (heaps (CONS (NTP4VCBinomialMergeTree e c rnk) r) <=>
           le_roots e c /\ heaps c /\ heaps r)) /\
       (!x:A. occ x [] = (&0:int)) /\
       (!x y:A.
        !c:(A ntp4vc_binomial_merge_tree)list.
        !rnk:int.
        !r:(A ntp4vc_binomial_merge_tree)list.
          occ x (CONS (NTP4VCBinomialMergeTree y c rnk) r) =
          (if x = y then (&1:int) else (&0:int)) +
          occ x c + occ x r) /\
       (!m:int. has_order m [] <=> m = (&0:int)) /\
       (!m:int.
        !x:A.
        !c:(A ntp4vc_binomial_merge_tree)list.
        !rnk:int.
        !r:(A ntp4vc_binomial_merge_tree)list.
          (has_order m
             (CONS (NTP4VCBinomialMergeTree x c rnk) r) <=>
           rnk = m - (&1:int) /\
           has_order (m - (&1:int)) c /\
           has_order (m - (&1:int)) r)) /\
       (!m:int. heap_inv m [] <=> T) /\
       (!m:int.
        !t:A ntp4vc_binomial_merge_tree.
        !r:(A ntp4vc_binomial_merge_tree)list.
          (heap_inv m (CONS t r) <=>
           m <= rank t /\
           binomial_tree t /\
           heap_inv (rank t + (&1:int)) r))) in
    background
    ==> heaps h1
    ==> heap_inv k h1
    ==> heaps h2
    ==> heap_inv k h2
    ==> merge_step /\
        (!result:(A ntp4vc_binomial_merge_tree)list.
           result_case result
           ==>
           heaps result /\
           heap_inv k result /\
           (!x:A. occ x result = occ x h1 + occ x h2))`;;

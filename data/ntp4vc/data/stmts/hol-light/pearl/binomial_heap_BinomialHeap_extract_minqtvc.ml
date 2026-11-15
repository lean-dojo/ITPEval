(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/binomial_heap_BinomialHeap_extract_minqtvc: a binomial-heap
  extract-min verification condition preserving heap order and rank
  invariants while updating element multiplicities after the minimum tree's
  children are reversed and merged with the remaining heap. This file
  contains no proof.
*)

let ntp4vc_binomial_heap_tree_INDUCT,ntp4vc_binomial_heap_tree_RECURSION =
  define_type
    "ntp4vc_binomial_heap_tree =
       NTP4VCBinomialHeapTree A (ntp4vc_binomial_heap_tree list) int";;

let statement =
 `!le:A->A->bool.
  !elem:A ntp4vc_binomial_heap_tree->A.
  !children:A ntp4vc_binomial_heap_tree->
    (A ntp4vc_binomial_heap_tree)list.
  !rank:A ntp4vc_binomial_heap_tree->int.
  !le_roots:A->(A ntp4vc_binomial_heap_tree)list->bool.
  !heaps:(A ntp4vc_binomial_heap_tree)list->bool.
  !occ:A->(A ntp4vc_binomial_heap_tree)list->int.
  !has_order:int->(A ntp4vc_binomial_heap_tree)list->bool.
  !heap_inv:int->(A ntp4vc_binomial_heap_tree)list->bool.
  !h:(A ntp4vc_binomial_heap_tree)list.
    let binomial_tree =
      \t:A ntp4vc_binomial_heap_tree.
        rank t = (&(LENGTH (children t)):int) /\
        has_order (rank t) (children t) in
    let background =
      ((!x:A. le x x) /\
       (!x y z:A. le x y /\ le y z ==> le x z) /\
       (!x y:A. le x y \/ le y x) /\
       (!e:A.
        !c:(A ntp4vc_binomial_heap_tree)list.
        !r:int.
          elem (NTP4VCBinomialHeapTree e c r) = e /\
          children (NTP4VCBinomialHeapTree e c r) = c /\
          rank (NTP4VCBinomialHeapTree e c r) = r) /\
       (!e:A. le_roots e [] <=> T) /\
       (!e:A.
        !t:A ntp4vc_binomial_heap_tree.
        !r:(A ntp4vc_binomial_heap_tree)list.
          (le_roots e (CONS t r) <=>
           le e (elem t) /\ le_roots e r)) /\
       (heaps [] <=> T) /\
       (!e:A.
        !c:(A ntp4vc_binomial_heap_tree)list.
        !rnk:int.
        !r:(A ntp4vc_binomial_heap_tree)list.
          (heaps (CONS (NTP4VCBinomialHeapTree e c rnk) r) <=>
           le_roots e c /\ heaps c /\ heaps r)) /\
       (!x:A. occ x [] = (&0:int)) /\
       (!x y:A.
        !c:(A ntp4vc_binomial_heap_tree)list.
        !rnk:int.
        !r:(A ntp4vc_binomial_heap_tree)list.
          occ x (CONS (NTP4VCBinomialHeapTree y c rnk) r) =
          (if x = y then (&1:int) else (&0:int)) +
          occ x c + occ x r) /\
       (!k:int. has_order k [] <=> k = (&0:int)) /\
       (!k:int.
        !x:A.
        !c:(A ntp4vc_binomial_heap_tree)list.
        !rnk:int.
        !r:(A ntp4vc_binomial_heap_tree)list.
          (has_order k
             (CONS (NTP4VCBinomialHeapTree x c rnk) r) <=>
           rnk = k - (&1:int) /\
           has_order (k - (&1:int)) c /\
           has_order (k - (&1:int)) r)) /\
       (!m:int. heap_inv m [] <=> T) /\
       (!m:int.
        !t:A ntp4vc_binomial_heap_tree.
        !r:(A ntp4vc_binomial_heap_tree)list.
          (heap_inv m (CONS t r) <=>
           m <= rank t /\
           binomial_tree t /\
           heap_inv (rank t + (&1:int)) r))) in
    background
    ==> heaps h
    ==> heap_inv (&0:int) h
    ==> ~(h = [])
    ==> heaps h /\
        heap_inv (&0:int) h /\
        ~(h = []) /\
        (!t:A ntp4vc_binomial_heap_tree.
         !h':(A ntp4vc_binomial_heap_tree)list.
           heaps [t] /\
           heaps h' /\
           heap_inv (&0:int) h' /\
           le_roots (elem t) h /\
           binomial_tree t /\
           (!x:A. occ x h = occ x [t] + occ x h')
           ==>
           (let o1 = REVERSE (children t) in
              heaps o1 /\
              heap_inv (&0:int) o1 /\
              heaps h' /\
              heap_inv (&0:int) h') /\
           (!h'1:(A ntp4vc_binomial_heap_tree)list.
              heaps h'1 /\
              heap_inv (&0:int) h'1 /\
              (!x:A.
                 occ x h'1 =
                 occ x (REVERSE (children t)) + occ x h')
              ==>
              heaps h'1 /\
              heap_inv (&0:int) h'1 /\
              occ (elem t) h'1 = occ (elem t) h - (&1:int) /\
              (!x:A.
                 ~(x = elem t)
                 ==> occ x h'1 = occ x h)))`;;

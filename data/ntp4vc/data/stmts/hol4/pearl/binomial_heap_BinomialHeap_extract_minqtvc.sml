(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/binomial_heap_BinomialHeap_extract_minqtvc: a binomial-heap
  minimum-extraction verification condition preserving heap and rank
  invariants and accounting for the removed root by element multiplicity.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  binomial_heap_tree =
    BinomialHeapTree 'elt (binomial_heap_tree list) int
End

val binomial_heap_elem_def = Define `
  binomial_heap_elem (BinomialHeapTree e children k) = e`;

val binomial_heap_children_def = Define `
  binomial_heap_children (BinomialHeapTree e children k) = children`;

val binomial_heap_rank_def = Define `
  binomial_heap_rank (BinomialHeapTree e children k) = k`;

val binomial_heap_binomial_tree_def = Define `
  binomial_heap_binomial_tree has_order t <=>
    binomial_heap_rank t =
      &(LENGTH (binomial_heap_children t)) /\
    has_order
      (binomial_heap_rank t)
      (binomial_heap_children t)`;

val binomial_heap_BinomialHeap_extract_min_vc =
  ``!(le : 'elt -> 'elt -> bool)
      (le_roots :
        'elt -> ('elt binomial_heap_tree) list -> bool)
      (heaps : ('elt binomial_heap_tree) list -> bool)
      (occ :
        'elt -> ('elt binomial_heap_tree) list -> int)
      (has_order :
        int -> ('elt binomial_heap_tree) list -> bool)
      (inv :
        int -> ('elt binomial_heap_tree) list -> bool)
      (h : ('elt binomial_heap_tree) list).
      (!x. le x x) ==>
      (!x y z. le x y /\ le y z ==> le x z) ==>
      (!x y. le x y \/ le y x) ==>
      (!e. le_roots e [] = T) ==>
      (!e t r.
         le_roots e (t :: r) =
           (le e (binomial_heap_elem t) /\
            le_roots e r)) ==>
      (heaps [] = T) ==>
      (!e c k r.
         heaps (BinomialHeapTree e c k :: r) =
           (le_roots e c /\ heaps c /\ heaps r)) ==>
      (!x. occ x [] = 0) ==>
      (!x y c k r.
         occ x (BinomialHeapTree y c k :: r) =
           (if x = y then 1 else 0) +
             occ x c + occ x r) ==>
      (!k. has_order k [] = (k = 0)) ==>
      (!k x c k' r.
         has_order k (BinomialHeapTree x c k' :: r) =
           (k' = k - 1 /\
            has_order (k - 1) c /\
            has_order (k - 1) r)) ==>
      (!m. inv m [] = T) ==>
      (!m t r.
         inv m (t :: r) =
           (m <= binomial_heap_rank t /\
            binomial_heap_binomial_tree has_order t /\
            inv (binomial_heap_rank t + 1) r)) ==>
      heaps h ==>
      inv 0 h ==>
      ~(h = []) ==>
      heaps h /\
      inv 0 h /\
      ~(h = []) /\
      !t h'.
        (heaps (t :: []) /\
         heaps h' /\
         inv 0 h' /\
         le_roots (binomial_heap_elem t) h /\
         binomial_heap_binomial_tree has_order t /\
         (!x.
            occ x h =
              occ x (t :: []) + occ x h'))
        ==>
        (let o1 = REVERSE (binomial_heap_children t)
         in
           heaps o1 /\
           inv 0 o1 /\
           heaps h' /\
           inv 0 h') /\
        !h1.
          (heaps h1 /\
           inv 0 h1 /\
           (!x.
              occ x h1 =
                occ x (REVERSE (binomial_heap_children t)) +
                  occ x h'))
          ==>
          heaps h1 /\
          inv 0 h1 /\
          occ (binomial_heap_elem t) h1 =
            occ (binomial_heap_elem t) h - 1 /\
          !x.
            ~(x = binomial_heap_elem t) ==>
            occ x h1 = occ x h``;

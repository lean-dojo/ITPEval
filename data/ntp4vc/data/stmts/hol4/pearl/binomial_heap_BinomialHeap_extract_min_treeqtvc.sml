(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/binomial_heap_BinomialHeap_extract_min_treeqtvc: a binomial-heap
  extraction verification condition preserving heap and rank invariants,
  root minimality, binomial-tree structure, and element multiplicities.
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

val binomial_heap_BinomialHeap_extract_min_tree_vc =
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
      (h : ('elt binomial_heap_tree) list)
      (k : int).
      (!x. le x x) ==>
      (!x y z. le x y /\ le y z ==> le x z) ==>
      (!x y. le x y \/ le y x) ==>
      (!e. le_roots e [] = T) ==>
      (!e t r.
         le_roots e (t :: r) =
           (le e (binomial_heap_elem t) /\
            le_roots e r)) ==>
      (heaps [] = T) ==>
      (!e c k0 r.
         heaps (BinomialHeapTree e c k0 :: r) =
           (le_roots e c /\ heaps c /\ heaps r)) ==>
      (!x. occ x [] = 0) ==>
      (!x y c k0 r.
         occ x (BinomialHeapTree y c k0 :: r) =
           (if x = y then 1 else 0) +
             occ x c + occ x r) ==>
      (!k0. has_order k0 [] = (k0 = 0)) ==>
      (!k0 x c k1 r.
         has_order k0 (BinomialHeapTree x c k1 :: r) =
           (k1 = k0 - 1 /\
            has_order (k0 - 1) c /\
            has_order (k0 - 1) r)) ==>
      (!m. inv m [] = T) ==>
      (!m t r.
         inv m (t :: r) =
           (m <= binomial_heap_rank t /\
            binomial_heap_binomial_tree has_order t /\
            inv (binomial_heap_rank t + 1) r)) ==>
      heaps h ==>
      inv k h ==>
      ~(h = []) ==>
      ((case h of
          [] => F
        | t :: [] => T
        | t :: tl =>
            (case h of
               [] => F
             | _ :: f => f = tl) /\
            heaps tl /\
            inv (binomial_heap_rank t + 1) tl /\
            ~(tl = [])) /\
       !t h'.
         (case h of
            [] => F
          | t1 :: [] => t = t1 /\ h' = []
          | t1 :: tl =>
              ?t2 h1.
                (heaps (t2 :: []) /\
                 heaps h1 /\
                 inv (binomial_heap_rank t1 + 1) h1 /\
                 le_roots (binomial_heap_elem t2) tl /\
                 binomial_heap_binomial_tree has_order t2 /\
                 (!x.
                    occ x tl =
                      occ x (t2 :: []) + occ x h1)) /\
                (if le
                      (binomial_heap_elem t1)
                      (binomial_heap_elem t2)
                 then t = t1 /\ h' = tl
                 else t = t2 /\ h' = t1 :: h1))
         ==>
         heaps (t :: []) /\
         heaps h' /\
         inv k h' /\
         le_roots (binomial_heap_elem t) h /\
         binomial_heap_binomial_tree has_order t /\
         (!x.
            occ x h =
              occ x (t :: []) + occ x h'))``;

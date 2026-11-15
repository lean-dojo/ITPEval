(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/binomial_heap_BinomialHeap_mergeqtvc: a binomial-heap merge
  verification condition capturing merge branches, tree linking, heap and
  rank invariants, and additive element multiplicities.
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

val binomial_heap_link_def = Define `
  binomial_heap_link le t1 t2 =
    if le
         (binomial_heap_elem t1)
         (binomial_heap_elem t2)
    then
      BinomialHeapTree
        (binomial_heap_elem t1)
        (t2 :: binomial_heap_children t1)
        (binomial_heap_rank t1 + 1)
    else
      BinomialHeapTree
        (binomial_heap_elem t2)
        (t1 :: binomial_heap_children t2)
        (binomial_heap_rank t2 + 1)`;

val binomial_heap_BinomialHeap_merge_vc =
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
      (h1 : ('elt binomial_heap_tree) list)
      (k : int)
      (h2 : ('elt binomial_heap_tree) list).
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
      heaps h1 ==>
      inv k h1 ==>
      heaps h2 ==>
      inv k h2 ==>
      ((case h2 of
          [] =>
            (case h1 of
               [] => T
             | _ => T)
        | x :: x1 =>
            (case h1 of
               [] => T
             | x2 :: x3 =>
                 if binomial_heap_rank x2 < binomial_heap_rank x
                 then
                   let o1 = binomial_heap_rank x2 + 1
                   in
                     (case h1 of
                        [] => F
                      | _ :: f => f = x3) /\
                     heaps x3 /\
                     inv o1 x3 /\
                     heaps h2 /\
                     inv o1 h2
                 else if binomial_heap_rank x <
                         binomial_heap_rank x2
                 then
                   let o1 = binomial_heap_rank x + 1
                   in
                     (case h2 of
                        [] => F
                      | _ :: f => f = x1) /\
                     heaps h1 /\
                     inv o1 h1 /\
                     heaps x1 /\
                     inv o1 x1
                 else
                   let o1 = binomial_heap_rank x2 + 1
                   in
                     (((case h1 of
                          [] => F
                        | _ :: f => f = x3) \/
                       h1 = x3 /\
                       (case h2 of
                          [] => F
                        | _ :: f => f = x1)) /\
                      heaps x3 /\
                      inv o1 x3 /\
                      heaps x1 /\
                      inv o1 x1) /\
                     !o2.
                       heaps o2 /\
                       inv o1 o2 /\
                       (!x4.
                          occ x4 o2 =
                            occ x4 x3 + occ x4 x1)
                       ==>
                       (let o3 =
                          binomial_heap_link le x2 x
                        in
                          heaps (o3 :: []) /\
                          binomial_heap_binomial_tree
                            has_order o3 /\
                          heaps o2 /\
                          inv (binomial_heap_rank o3) o2))) /\
       !result.
         (case h2 of
            [] =>
              (case h1 of
                 [] => result = h2
               | _ => result = h1)
          | x :: x1 =>
              (case h1 of
                 [] => result = h2
               | x2 :: x3 =>
                   if binomial_heap_rank x2 <
                        binomial_heap_rank x
                   then
                     ?o1.
                       (heaps o1 /\
                        inv (binomial_heap_rank x2 + 1) o1 /\
                        (!x4.
                           occ x4 o1 =
                             occ x4 x3 + occ x4 h2)) /\
                       result = x2 :: o1
                   else if binomial_heap_rank x <
                           binomial_heap_rank x2
                   then
                     ?o1.
                       (heaps o1 /\
                        inv (binomial_heap_rank x + 1) o1 /\
                        (!x4.
                           occ x4 o1 =
                             occ x4 h1 + occ x4 x1)) /\
                       result = x :: o1
                   else
                     ?o1.
                       (heaps o1 /\
                        inv (binomial_heap_rank x2 + 1) o1 /\
                        (!x4.
                           occ x4 o1 =
                             occ x4 x3 + occ x4 x1)) /\
                       (let o2 =
                          binomial_heap_link le x2 x
                        in
                          heaps result /\
                          inv (binomial_heap_rank o2) result /\
                          !x4.
                            occ x4 result =
                              occ x4 (o2 :: []) +
                                occ x4 o1)))
         ==>
         heaps result /\
         inv k result /\
         !x.
           occ x result =
             occ x h1 + occ x h2)``;

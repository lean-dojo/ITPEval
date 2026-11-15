(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/binomial_heap_BinomialHeap_get_minqtvc: a binomial-heap minimum
  verification condition establishing the scan invariant and that the
  returned element is a least member of the nonempty heap forest.
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

val binomial_heap_mem_def = Define `
  binomial_heap_mem occ x l <=> 0 < occ x l`;

val binomial_heap_BinomialHeap_get_min_vc =
  ``!(le : 'elt -> 'elt -> bool)
      (le_roots :
        'elt -> ('elt binomial_heap_tree) list -> bool)
      (heaps : ('elt binomial_heap_tree) list -> bool)
      (occ :
        'elt -> ('elt binomial_heap_tree) list -> int)
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
      heaps h ==>
      ~(h = []) ==>
      (case h of
         [] => F
       | t :: l =>
           ((!m l1.
               heaps l1 ==>
               (case l1 of
                  [] => T
                | BinomialHeapTree x c k :: r =>
                    !o1.
                      (if le x m then o1 = x else o1 = m) ==>
                      (case l1 of
                         [] => F
                       | _ :: f => f = r) /\
                      heaps r) /\
               !result.
                 (case l1 of
                    [] => result = m
                  | BinomialHeapTree x c k :: r =>
                      ?o1.
                        (if le x m then o1 = x else o1 = m) /\
                        (result = o1 \/
                         binomial_heap_mem occ result r) /\
                        le result o1 /\
                        !x1.
                          binomial_heap_mem occ x1 r ==>
                          le result x1)
                 ==>
                 (result = m \/
                  binomial_heap_mem occ result l1) /\
                 le result m /\
                 !x.
                   binomial_heap_mem occ x l1 ==>
                   le result x) /\
            heaps l) /\
           !result.
             (case h of
                [] => F
              | t0 :: l0 =>
                  let o1 = binomial_heap_elem t0
                  in
                    (result = o1 \/
                     binomial_heap_mem occ result l0) /\
                    le result o1 /\
                    !x.
                      binomial_heap_mem occ x l0 ==>
                      le result x)
             ==>
             binomial_heap_mem occ result h /\
             !x.
               binomial_heap_mem occ x h ==>
               le result x)``;

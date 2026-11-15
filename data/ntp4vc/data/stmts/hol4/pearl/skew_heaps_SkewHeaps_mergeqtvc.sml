(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/skew_heaps_SkewHeaps_mergeqtvc: the recursive skew-heap merge
  verification condition, including its termination obligations and
  preservation of heap order, element multiplicities, and total size.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  skew_heaps_merge_tree =
    SkewHeapsMergeEmpty
  | SkewHeapsMergeNode
      skew_heaps_merge_tree 'elt skew_heaps_merge_tree
End

val skew_heaps_merge_size_def = Define `
  (skew_heaps_merge_size
      (SkewHeapsMergeEmpty : 'elt skew_heaps_merge_tree) = (0 : int)) /\
  (skew_heaps_merge_size (SkewHeapsMergeNode l x r) =
     (1 : int) + skew_heaps_merge_size l + skew_heaps_merge_size r)`;

val skew_heaps_merge_occ_def = Define `
  (skew_heaps_merge_occ x
      (SkewHeapsMergeEmpty : 'elt skew_heaps_merge_tree) = (0 : int)) /\
  (skew_heaps_merge_occ x (SkewHeapsMergeNode l y r) =
     (if y = x then (1 : int) else (0 : int)) +
       skew_heaps_merge_occ x l + skew_heaps_merge_occ x r)`;

val skew_heaps_merge_le_root_def = Define `
  (skew_heaps_merge_le_root le e
      (SkewHeapsMergeEmpty : 'elt skew_heaps_merge_tree) = T) /\
  (skew_heaps_merge_le_root le e (SkewHeapsMergeNode l x r) =
     le e x)`;

val skew_heaps_merge_heap_def = Define `
  (skew_heaps_merge_heap le
      (SkewHeapsMergeEmpty : 'elt skew_heaps_merge_tree) = T) /\
  (skew_heaps_merge_heap le (SkewHeapsMergeNode l x r) =
     (skew_heaps_merge_le_root le x l /\
      skew_heaps_merge_heap le l /\
      skew_heaps_merge_le_root le x r /\
      skew_heaps_merge_heap le r))`;

val skew_heaps_SkewHeaps_merge_vc =
  ``!(le : 'elt -> 'elt -> bool)
      (t1 : 'elt skew_heaps_merge_tree)
      (t2 : 'elt skew_heaps_merge_tree).
      (!x. le x x) ==>
      (!x y z. le x y /\ le y z ==> le x z) ==>
      (!x y. le x y \/ le y x) ==>
      skew_heaps_merge_heap le t1 ==>
      skew_heaps_merge_heap le t2 ==>
      ((case t2 of
          SkewHeapsMergeEmpty =>
            (case t1 of
               SkewHeapsMergeEmpty => T
             | _ => T)
        | SkewHeapsMergeNode x x1 x2 =>
            (case t1 of
               SkewHeapsMergeEmpty => T
             | SkewHeapsMergeNode x3 x4 x5 =>
                 if le x4 x1
                 then
                   ((0 : int) <=
                      skew_heaps_merge_size t1 +
                        skew_heaps_merge_size t2 /\
                    skew_heaps_merge_size x5 +
                        skew_heaps_merge_size t2 <
                      skew_heaps_merge_size t1 +
                        skew_heaps_merge_size t2) /\
                   skew_heaps_merge_heap le x5 /\
                   skew_heaps_merge_heap le t2
                 else
                   ((0 : int) <=
                      skew_heaps_merge_size t1 +
                        skew_heaps_merge_size t2 /\
                   skew_heaps_merge_size x2 +
                        skew_heaps_merge_size t1 <
                      skew_heaps_merge_size t1 +
                        skew_heaps_merge_size t2) /\
                   skew_heaps_merge_heap le x2 /\
                   skew_heaps_merge_heap le t1)) /\
       !result.
         (case t2 of
            SkewHeapsMergeEmpty =>
              (case t1 of
                 SkewHeapsMergeEmpty => result = t2
               | _ => result = t1)
          | SkewHeapsMergeNode x x1 x2 =>
              (case t1 of
                 SkewHeapsMergeEmpty => result = t2
               | SkewHeapsMergeNode x3 x4 x5 =>
                   if le x4 x1
                   then
                     ?o1.
                       (skew_heaps_merge_heap le o1 /\
                        (!e.
                           skew_heaps_merge_occ e o1 =
                             skew_heaps_merge_occ e x5 +
                               skew_heaps_merge_occ e t2) /\
                        skew_heaps_merge_size o1 =
                          skew_heaps_merge_size x5 +
                            skew_heaps_merge_size t2) /\
                       result = SkewHeapsMergeNode o1 x4 x3
                   else
                     ?o1.
                       (skew_heaps_merge_heap le o1 /\
                        (!e.
                           skew_heaps_merge_occ e o1 =
                             skew_heaps_merge_occ e x2 +
                               skew_heaps_merge_occ e t1) /\
                        skew_heaps_merge_size o1 =
                          skew_heaps_merge_size x2 +
                            skew_heaps_merge_size t1) /\
                       result = SkewHeapsMergeNode o1 x1 x))
         ==>
         skew_heaps_merge_heap le result /\
         (!e.
            skew_heaps_merge_occ e result =
              skew_heaps_merge_occ e t1 +
                skew_heaps_merge_occ e t2) /\
         skew_heaps_merge_size result =
           skew_heaps_merge_size t1 +
             skew_heaps_merge_size t2)``;

(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/leftist_heap_LeftistHeap_mergeqtvc: a leftist-heap merge
  verification condition preserving total size, element multiplicities,
  heap order, and the leftist invariant. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  leftist_merge_tree =
    LeftistMergeEmpty
  | LeftistMergeNode int leftist_merge_tree 'elt leftist_merge_tree
End

val leftist_merge_size_def = Define `
  (leftist_merge_size
      (LeftistMergeEmpty : 'elt leftist_merge_tree) = (0 : int)) /\
  (leftist_merge_size (LeftistMergeNode s l x r) =
     (1 : int) + leftist_merge_size l + leftist_merge_size r)`;

val leftist_merge_occ_def = Define `
  (leftist_merge_occ x
      (LeftistMergeEmpty : 'elt leftist_merge_tree) = (0 : int)) /\
  (leftist_merge_occ x (LeftistMergeNode s l y r) =
     (if x = y then (1 : int) else (0 : int)) +
       leftist_merge_occ x l + leftist_merge_occ x r)`;

val leftist_merge_le_root_def = Define `
  (leftist_merge_le_root le e
      (LeftistMergeEmpty : 'elt leftist_merge_tree) = T) /\
  (leftist_merge_le_root le e (LeftistMergeNode s l x r) =
     le e x)`;

val leftist_merge_is_heap_def = Define `
  (leftist_merge_is_heap le
      (LeftistMergeEmpty : 'elt leftist_merge_tree) = T) /\
  (leftist_merge_is_heap le (LeftistMergeNode s l x r) =
     (leftist_merge_le_root le x l /\
      leftist_merge_is_heap le l /\
      leftist_merge_le_root le x r /\
      leftist_merge_is_heap le r))`;

val leftist_merge_rank_def = Define `
  (leftist_merge_rank
      (LeftistMergeEmpty : 'elt leftist_merge_tree) = (0 : int)) /\
  (leftist_merge_rank (LeftistMergeNode s l x r) =
     (1 : int) +
       if leftist_merge_rank l <= leftist_merge_rank r
       then leftist_merge_rank l
       else leftist_merge_rank r)`;

val leftist_merge_leftist_def = Define `
  (leftist_merge_leftist
      (LeftistMergeEmpty : 'elt leftist_merge_tree) = T) /\
  (leftist_merge_leftist (LeftistMergeNode s l x r) =
     (s = leftist_merge_rank (LeftistMergeNode s l x r) /\
      leftist_merge_leftist l /\
      leftist_merge_leftist r /\
      leftist_merge_rank r <= leftist_merge_rank l))`;

val leftist_merge_leftist_heap_def = Define `
  leftist_merge_leftist_heap le h <=>
    leftist_merge_is_heap le h /\ leftist_merge_leftist h`;

val leftist_heap_LeftistHeap_merge_vc =
  ``!(le : 'elt -> 'elt -> bool)
      (minimum : 'elt leftist_merge_tree -> 'elt)
      (h1 : 'elt leftist_merge_tree)
      (h2 : 'elt leftist_merge_tree).
      (!x. le x x) ==>
      (!x y z. le x y /\ le y z ==> le x z) ==>
      (!x y. le x y \/ le y x) ==>
      (!s l x r. minimum (LeftistMergeNode s l x r) = x) ==>
      leftist_merge_leftist_heap le h1 ==>
      leftist_merge_leftist_heap le h2 ==>
      ((case h2 of
          LeftistMergeEmpty =>
            (case h1 of
               LeftistMergeEmpty => T
             | _ => T)
        | LeftistMergeNode x x1 x2 x3 =>
            (case h1 of
               LeftistMergeEmpty => T
             | LeftistMergeNode x4 x5 x6 x7 =>
                 if le x6 x2
                 then
                   ((((0 : int) <=
                        leftist_merge_size h1 +
                          leftist_merge_size h2 /\
                      leftist_merge_size x7 +
                          leftist_merge_size h2 <
                        leftist_merge_size h1 +
                          leftist_merge_size h2) /\
                     leftist_merge_leftist_heap le x7 /\
                     leftist_merge_leftist_heap le h2) /\
                    (!o1.
                      (leftist_merge_size o1 =
                         leftist_merge_size x7 +
                           leftist_merge_size h2 /\
                       (!x8.
                          leftist_merge_occ x8 o1 =
                            leftist_merge_occ x8 x7 +
                              leftist_merge_occ x8 h2) /\
                       leftist_merge_leftist_heap le o1)
                      ==>
                      (leftist_merge_leftist_heap le o1 /\
                       leftist_merge_leftist_heap le x5) /\
                      leftist_merge_le_root le x6 x5 /\
                      leftist_merge_le_root le x6 o1))
                 else
                   ((((0 : int) <=
                        leftist_merge_size h1 +
                          leftist_merge_size h2 /\
                      leftist_merge_size h1 +
                          leftist_merge_size x3 <
                        leftist_merge_size h1 +
                          leftist_merge_size h2) /\
                     leftist_merge_leftist_heap le h1 /\
                     leftist_merge_leftist_heap le x3) /\
                    (!o1.
                      (leftist_merge_size o1 =
                         leftist_merge_size h1 +
                           leftist_merge_size x3 /\
                       (!x8.
                          leftist_merge_occ x8 o1 =
                            leftist_merge_occ x8 h1 +
                              leftist_merge_occ x8 x3) /\
                       leftist_merge_leftist_heap le o1)
                      ==>
                      (leftist_merge_leftist_heap le o1 /\
                       leftist_merge_leftist_heap le x1) /\
                      leftist_merge_le_root le x2 x1 /\
                      leftist_merge_le_root le x2 o1)))) /\
       !result.
         (case h2 of
            LeftistMergeEmpty =>
              (case h1 of
                 LeftistMergeEmpty => result = h1
               | _ => result = h1)
          | LeftistMergeNode x x1 x2 x3 =>
              (case h1 of
                 LeftistMergeEmpty => result = h2
               | LeftistMergeNode x4 x5 x6 x7 =>
                   if le x6 x2
                   then
                     ?o1.
                       (leftist_merge_size o1 =
                          leftist_merge_size x7 +
                            leftist_merge_size h2 /\
                        (!x8.
                           leftist_merge_occ x8 o1 =
                             leftist_merge_occ x8 x7 +
                               leftist_merge_occ x8 h2) /\
                        leftist_merge_leftist_heap le o1) /\
                       leftist_merge_leftist_heap le result /\
                       minimum result = x6 /\
                       leftist_merge_size result =
                         (1 : int) + leftist_merge_size x5 +
                           leftist_merge_size o1 /\
                       leftist_merge_occ x6 result =
                         (1 : int) + leftist_merge_occ x6 x5 +
                           leftist_merge_occ x6 o1 /\
                       (!y.
                          ~(x6 = y) ==>
                          leftist_merge_occ y result =
                            leftist_merge_occ y x5 +
                              leftist_merge_occ y o1)
                   else
                     ?o1.
                       (leftist_merge_size o1 =
                          leftist_merge_size h1 +
                            leftist_merge_size x3 /\
                        (!x8.
                           leftist_merge_occ x8 o1 =
                             leftist_merge_occ x8 h1 +
                               leftist_merge_occ x8 x3) /\
                        leftist_merge_leftist_heap le o1) /\
                       leftist_merge_leftist_heap le result /\
                       minimum result = x2 /\
                       leftist_merge_size result =
                         (1 : int) + leftist_merge_size x1 +
                           leftist_merge_size o1 /\
                       leftist_merge_occ x2 result =
                         (1 : int) + leftist_merge_occ x2 x1 +
                           leftist_merge_occ x2 o1 /\
                       (!y.
                          ~(x2 = y) ==>
                          leftist_merge_occ y result =
                            leftist_merge_occ y x1 +
                              leftist_merge_occ y o1)))
         ==>
         leftist_merge_size result =
           leftist_merge_size h1 + leftist_merge_size h2 /\
         (!x.
            leftist_merge_occ x result =
              leftist_merge_occ x h1 + leftist_merge_occ x h2) /\
         leftist_merge_leftist_heap le result)``;

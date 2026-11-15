(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/leftist_heap_LeftistHeap_delete_minqtvc: a leftist-heap
  delete-minimum verification condition preserving heap and leftist
  invariants while removing exactly one occurrence of the minimum.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  leftist_delete_tree =
    LeftistDeleteEmpty
  | LeftistDeleteNode int leftist_delete_tree 'elt leftist_delete_tree
End

val leftist_delete_size_def = Define `
  (leftist_delete_size
      (LeftistDeleteEmpty : 'elt leftist_delete_tree) = (0 : int)) /\
  (leftist_delete_size (LeftistDeleteNode s l x r) =
     (1 : int) + leftist_delete_size l + leftist_delete_size r)`;

val leftist_delete_occ_def = Define `
  (leftist_delete_occ x
      (LeftistDeleteEmpty : 'elt leftist_delete_tree) = (0 : int)) /\
  (leftist_delete_occ x (LeftistDeleteNode s l y r) =
     (if x = y then (1 : int) else (0 : int)) +
       leftist_delete_occ x l + leftist_delete_occ x r)`;

val leftist_delete_le_root_def = Define `
  (leftist_delete_le_root le e
      (LeftistDeleteEmpty : 'elt leftist_delete_tree) = T) /\
  (leftist_delete_le_root le e (LeftistDeleteNode s l x r) =
     le e x)`;

val leftist_delete_is_heap_def = Define `
  (leftist_delete_is_heap le
      (LeftistDeleteEmpty : 'elt leftist_delete_tree) = T) /\
  (leftist_delete_is_heap le (LeftistDeleteNode s l x r) =
     (leftist_delete_le_root le x l /\
      leftist_delete_is_heap le l /\
      leftist_delete_le_root le x r /\
      leftist_delete_is_heap le r))`;

val leftist_delete_rank_def = Define `
  (leftist_delete_rank
      (LeftistDeleteEmpty : 'elt leftist_delete_tree) = (0 : int)) /\
  (leftist_delete_rank (LeftistDeleteNode s l x r) =
     (1 : int) +
       if leftist_delete_rank l <= leftist_delete_rank r
       then leftist_delete_rank l
       else leftist_delete_rank r)`;

val leftist_delete_leftist_def = Define `
  (leftist_delete_leftist
      (LeftistDeleteEmpty : 'elt leftist_delete_tree) = T) /\
  (leftist_delete_leftist (LeftistDeleteNode s l x r) =
     (s = leftist_delete_rank (LeftistDeleteNode s l x r) /\
      leftist_delete_leftist l /\
      leftist_delete_leftist r /\
      leftist_delete_rank r <= leftist_delete_rank l))`;

val leftist_delete_leftist_heap_def = Define `
  leftist_delete_leftist_heap le h <=>
    leftist_delete_is_heap le h /\ leftist_delete_leftist h`;

val leftist_heap_LeftistHeap_delete_min_vc =
  ``!(le : 'elt -> 'elt -> bool)
      (minimum : 'elt leftist_delete_tree -> 'elt)
      (h : 'elt leftist_delete_tree).
      (!x. le x x) ==>
      (!x y z. le x y /\ le y z ==> le x z) ==>
      (!x y. le x y \/ le y x) ==>
      (!s l x r. minimum (LeftistDeleteNode s l x r) = x) ==>
      (0 : int) < leftist_delete_size h ==>
      leftist_delete_leftist_heap le h ==>
      ((case h of
          LeftistDeleteEmpty => F
        | LeftistDeleteNode s l x r =>
            leftist_delete_leftist_heap le l /\
            leftist_delete_leftist_heap le r) /\
       !result.
         (case h of
            LeftistDeleteEmpty => F
          | LeftistDeleteNode s l x r =>
              leftist_delete_size result =
                leftist_delete_size l + leftist_delete_size r /\
              (!y.
                 leftist_delete_occ y result =
                   leftist_delete_occ y l + leftist_delete_occ y r) /\
              leftist_delete_leftist_heap le result)
         ==>
         leftist_delete_occ (minimum h) result =
           leftist_delete_occ (minimum h) h - (1 : int) /\
         (!y.
            ~(y = minimum h) ==>
            leftist_delete_occ y result = leftist_delete_occ y h) /\
         leftist_delete_size result =
           leftist_delete_size h - (1 : int) /\
         leftist_delete_leftist_heap le result)``;

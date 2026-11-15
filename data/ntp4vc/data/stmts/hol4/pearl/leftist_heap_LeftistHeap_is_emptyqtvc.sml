(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/leftist_heap_LeftistHeap_is_emptyqtvc: a leftist-tree emptiness
  verification condition equating the constructor-based Boolean result with
  zero recursive tree size. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  leftist_is_empty_tree =
    LeftistIsEmptyEmpty
  | LeftistIsEmptyNode int leftist_is_empty_tree 'elt leftist_is_empty_tree
End

val leftist_is_empty_size_def = Define `
  (leftist_is_empty_size
      (LeftistIsEmptyEmpty : 'elt leftist_is_empty_tree) = (0 : int)) /\
  (leftist_is_empty_size (LeftistIsEmptyNode s l x r) =
     (1 : int) + leftist_is_empty_size l + leftist_is_empty_size r)`;

val leftist_heap_LeftistHeap_is_empty_vc =
  ``!(h : 'elt leftist_is_empty_tree) (result : bool).
      (case h of
         LeftistIsEmptyEmpty => result = T
       | LeftistIsEmptyNode s l x r => result = F) ==>
      ((result = T) <=> leftist_is_empty_size h = (0 : int))``;

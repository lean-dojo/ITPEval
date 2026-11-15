(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/pairing_heap_PairingHeap_delete_minqtvc: a pairing-heap
  delete-minimum verification condition in which the child forest is
  well-formed and the result removes exactly one occurrence of the root
  minimum while preserving every other multiplicity and decreasing the size.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  pairing_delete_raw_heap =
    PairingDeleteEmpty
  | PairingDeleteHeap pairing_delete_tree
  ;
  pairing_delete_tree =
    PairingDeleteTree 'elt (pairing_delete_tree list)
End

val pairing_heap_PairingHeap_delete_min_vc =
  ``!(le : 'elt -> 'elt -> bool)
      (size_heap : 'elt pairing_delete_raw_heap -> int)
      (size_tree : 'elt pairing_delete_tree -> int)
      (size_list : ('elt pairing_delete_tree) list -> int)
      (occ_heap : 'elt -> 'elt pairing_delete_raw_heap -> int)
      (occ_tree : 'elt -> 'elt pairing_delete_tree -> int)
      (occ_list : 'elt -> ('elt pairing_delete_tree) list -> int)
      (le_roots : 'elt -> ('elt pairing_delete_tree) list -> bool)
      (heap : 'elt pairing_delete_raw_heap -> bool)
      (heap_tree : 'elt pairing_delete_tree -> bool)
      (heap_list : ('elt pairing_delete_tree) list -> bool)
      (h : 'heap -> 'elt pairing_delete_raw_heap)
      (minimum_tree : 'elt pairing_delete_tree -> 'elt)
      (minimum : 'elt pairing_delete_raw_heap -> 'elt)
      (empty : 'heap)
      (hh : 'heap).
      (!x. le x x) ==>
      (!x y z. le x y /\ le y z ==> le x z) ==>
      (!x y. le x y \/ le y x) ==>
      (size_heap PairingDeleteEmpty = (0 : int)) ==>
      (!t. size_heap (PairingDeleteHeap t) = size_tree t) ==>
      (!x l.
         size_tree (PairingDeleteTree x l) =
           (1 : int) + size_list l) ==>
      (size_list [] = (0 : int)) ==>
      (!t r. size_list (t :: r) = size_tree t + size_list r) ==>
      (!x. occ_heap x PairingDeleteEmpty = (0 : int)) ==>
      (!x t. occ_heap x (PairingDeleteHeap t) = occ_tree x t) ==>
      (!x e l.
         occ_tree x (PairingDeleteTree e l) =
           (if x = e then (1 : int) else (0 : int)) + occ_list x l) ==>
      (!x. occ_list x [] = (0 : int)) ==>
      (!x t r. occ_list x (t :: r) = occ_tree x t + occ_list x r) ==>
      (!e. le_roots e [] = T) ==>
      (!e x l r.
         le_roots e (PairingDeleteTree x l :: r) =
           (le e x /\ le_roots e r)) ==>
      (heap PairingDeleteEmpty = T) ==>
      (!t. heap (PairingDeleteHeap t) = heap_tree t) ==>
      (!x l.
         heap_tree (PairingDeleteTree x l) =
           (le_roots x l /\ heap_list l)) ==>
      (heap_list [] = T) ==>
      (!t r. heap_list (t :: r) = (heap_tree t /\ heap_list r)) ==>
      (!self. heap (h self)) ==>
      (!a b. h a = h b ==> a = b) ==>
      (!x l. minimum_tree (PairingDeleteTree x l) = x) ==>
      (!t. minimum (PairingDeleteHeap t) = minimum_tree t) ==>
      (size_heap (h empty) = (0 : int) /\
       (!e. ~((0 : int) < occ_heap e (h empty)))) ==>
      (0 : int) < size_heap (h hh) ==>
      (let o1 = h hh
       in
         (case o1 of
            PairingDeleteEmpty => F
          | PairingDeleteHeap (PairingDeleteTree x l) => heap_list l) /\
         !result.
           (case o1 of
              PairingDeleteEmpty => F
            | PairingDeleteHeap (PairingDeleteTree x l) =>
                size_heap (h result) = size_list l /\
                (!x. occ_heap x (h result) = occ_list x l))
           ==>
           occ_heap (minimum (h hh)) (h result) =
             occ_heap (minimum (h hh)) (h hh) - (1 : int) /\
           (!y.
              ~(y = minimum (h hh)) ==>
              occ_heap y (h result) = occ_heap y (h hh)) /\
           size_heap (h result) =
             size_heap (h hh) - (1 : int))``;

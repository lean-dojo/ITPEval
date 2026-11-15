(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/pairing_heap_PairingHeap_find_minqtvc: a pairing-heap find-minimum
  verification condition showing that a positive-size heap is nonempty and
  that its returned root is the abstract minimum. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  pairing_find_raw_heap =
    PairingFindEmpty
  | PairingFindHeap pairing_find_tree
  ;
  pairing_find_tree =
    PairingFindTree 'elt (pairing_find_tree list)
End

val pairing_heap_PairingHeap_find_min_vc =
  ``!(le : 'elt -> 'elt -> bool)
      (size_heap : 'elt pairing_find_raw_heap -> int)
      (size_tree : 'elt pairing_find_tree -> int)
      (size_list : ('elt pairing_find_tree) list -> int)
      (occ_heap : 'elt -> 'elt pairing_find_raw_heap -> int)
      (occ_tree : 'elt -> 'elt pairing_find_tree -> int)
      (occ_list : 'elt -> ('elt pairing_find_tree) list -> int)
      (le_roots : 'elt -> ('elt pairing_find_tree) list -> bool)
      (heap : 'elt pairing_find_raw_heap -> bool)
      (heap_tree : 'elt pairing_find_tree -> bool)
      (heap_list : ('elt pairing_find_tree) list -> bool)
      (h : 'heap -> 'elt pairing_find_raw_heap)
      (minimum_tree : 'elt pairing_find_tree -> 'elt)
      (minimum : 'elt pairing_find_raw_heap -> 'elt)
      (empty : 'heap)
      (hh : 'heap).
      (!x. le x x) ==>
      (!x y z. le x y /\ le y z ==> le x z) ==>
      (!x y. le x y \/ le y x) ==>
      (size_heap PairingFindEmpty = (0 : int)) ==>
      (!t. size_heap (PairingFindHeap t) = size_tree t) ==>
      (!x l.
         size_tree (PairingFindTree x l) =
           (1 : int) + size_list l) ==>
      (size_list [] = (0 : int)) ==>
      (!t r. size_list (t :: r) = size_tree t + size_list r) ==>
      (!x. occ_heap x PairingFindEmpty = (0 : int)) ==>
      (!x t. occ_heap x (PairingFindHeap t) = occ_tree x t) ==>
      (!x e l.
         occ_tree x (PairingFindTree e l) =
           (if x = e then (1 : int) else (0 : int)) + occ_list x l) ==>
      (!x. occ_list x [] = (0 : int)) ==>
      (!x t r. occ_list x (t :: r) = occ_tree x t + occ_list x r) ==>
      (!e. le_roots e [] = T) ==>
      (!e x l r.
         le_roots e (PairingFindTree x l :: r) =
           (le e x /\ le_roots e r)) ==>
      (heap PairingFindEmpty = T) ==>
      (!t. heap (PairingFindHeap t) = heap_tree t) ==>
      (!x l.
         heap_tree (PairingFindTree x l) =
           (le_roots x l /\ heap_list l)) ==>
      (heap_list [] = T) ==>
      (!t r. heap_list (t :: r) = (heap_tree t /\ heap_list r)) ==>
      (!self. heap (h self)) ==>
      (!a b. h a = h b ==> a = b) ==>
      (!x l. minimum_tree (PairingFindTree x l) = x) ==>
      (!t. minimum (PairingFindHeap t) = minimum_tree t) ==>
      (size_heap (h empty) = (0 : int) /\
       (!e. ~((0 : int) < occ_heap e (h empty)))) ==>
      (0 : int) < size_heap (h hh) ==>
      (let o1 = h hh
       in
         (case o1 of
            PairingFindEmpty => F
          | PairingFindHeap (PairingFindTree x l) => T) /\
         !result.
           (case o1 of
              PairingFindEmpty => F
            | PairingFindHeap (PairingFindTree x l) => result = x)
           ==>
           result = minimum (h hh))``;

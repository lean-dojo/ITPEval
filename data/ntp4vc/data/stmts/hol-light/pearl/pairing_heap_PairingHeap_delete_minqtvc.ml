(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/pairing_heap_PairingHeap_delete_minqtvc: a pairing-heap delete-min
  verification condition showing that merging the deleted root's children
  removes one occurrence of the minimum, preserves every other
  multiplicity, and decreases the heap size by one. This file contains no
  proof.
*)

let ntp4vc_pairing_delete_INDUCT,ntp4vc_pairing_delete_RECURSION =
  define_type
    "ntp4vc_pairing_delete_raw_heap =
       NTP4VCPairingDeleteEmpty
     | NTP4VCPairingDeleteHeap ntp4vc_pairing_delete_tree;
     ntp4vc_pairing_delete_tree =
       NTP4VCPairingDeleteTree
         A (ntp4vc_pairing_delete_tree list)";;

let statement =
 `!le:A->A->bool.
  !size_heap:A ntp4vc_pairing_delete_raw_heap->int.
  !size_tree:A ntp4vc_pairing_delete_tree->int.
  !size_list:(A ntp4vc_pairing_delete_tree)list->int.
  !occ_heap:A->A ntp4vc_pairing_delete_raw_heap->int.
  !occ_tree:A->A ntp4vc_pairing_delete_tree->int.
  !occ_list:A->(A ntp4vc_pairing_delete_tree)list->int.
  !le_tree:A->A ntp4vc_pairing_delete_tree->bool.
  !le_root:A->A ntp4vc_pairing_delete_raw_heap->bool.
  !le_roots:A->(A ntp4vc_pairing_delete_tree)list->bool.
  !heap:A ntp4vc_pairing_delete_raw_heap->bool.
  !heap_tree:A ntp4vc_pairing_delete_tree->bool.
  !heap_list:(A ntp4vc_pairing_delete_tree)list->bool.
  !heap_of:B->A ntp4vc_pairing_delete_raw_heap.
  !minimum_tree:A ntp4vc_pairing_delete_tree->A.
  !minimum:A ntp4vc_pairing_delete_raw_heap->A.
  !empty:B.
  !hh:B.
    ((!x:A. le x x) /\
     (!x y z:A. le x y /\ le y z ==> le x z) /\
     (!x y:A. le x y \/ le y x) /\
     size_heap NTP4VCPairingDeleteEmpty = (&0:int) /\
     (!t:A ntp4vc_pairing_delete_tree.
        size_heap (NTP4VCPairingDeleteHeap t) = size_tree t) /\
     (!x:A.
      !l:(A ntp4vc_pairing_delete_tree)list.
        size_tree (NTP4VCPairingDeleteTree x l) =
        (&1:int) + size_list l) /\
     size_list [] = (&0:int) /\
     (!t:A ntp4vc_pairing_delete_tree.
      !r:(A ntp4vc_pairing_delete_tree)list.
        size_list (CONS t r) = size_tree t + size_list r) /\
     (!x:A. occ_heap x NTP4VCPairingDeleteEmpty = (&0:int)) /\
     (!x:A.
      !t:A ntp4vc_pairing_delete_tree.
        occ_heap x (NTP4VCPairingDeleteHeap t) = occ_tree x t) /\
     (!x y:A.
      !l:(A ntp4vc_pairing_delete_tree)list.
        occ_tree x (NTP4VCPairingDeleteTree y l) =
        (if x = y then (&1:int) else (&0:int)) + occ_list x l) /\
     (!x:A. occ_list x [] = (&0:int)) /\
     (!x:A.
      !t:A ntp4vc_pairing_delete_tree.
      !r:(A ntp4vc_pairing_delete_tree)list.
        occ_list x (CONS t r) = occ_tree x t + occ_list x r) /\
     (!e x:A.
      !l:(A ntp4vc_pairing_delete_tree)list.
        le_tree e (NTP4VCPairingDeleteTree x l) = le e x) /\
     (!e:A. le_root e NTP4VCPairingDeleteEmpty = T) /\
     (!e:A.
      !t:A ntp4vc_pairing_delete_tree.
        le_root e (NTP4VCPairingDeleteHeap t) = le_tree e t) /\
     (!e:A. le_roots e [] = T) /\
     (!e:A.
      !t:A ntp4vc_pairing_delete_tree.
      !r:(A ntp4vc_pairing_delete_tree)list.
        le_roots e (CONS t r) = (le_tree e t /\ le_roots e r)) /\
     heap NTP4VCPairingDeleteEmpty = T /\
     (!t:A ntp4vc_pairing_delete_tree.
        heap (NTP4VCPairingDeleteHeap t) = heap_tree t) /\
     (!x:A.
      !l:(A ntp4vc_pairing_delete_tree)list.
        heap_tree (NTP4VCPairingDeleteTree x l) =
        (le_roots x l /\ heap_list l)) /\
     heap_list [] = T /\
     (!t:A ntp4vc_pairing_delete_tree.
      !r:(A ntp4vc_pairing_delete_tree)list.
        heap_list (CONS t r) = (heap_tree t /\ heap_list r)) /\
     (!self:B. heap (heap_of self)) /\
     (!a b:B. heap_of a = heap_of b ==> a = b) /\
     (!x:A.
      !l:(A ntp4vc_pairing_delete_tree)list.
        minimum_tree (NTP4VCPairingDeleteTree x l) = x) /\
     (!t:A ntp4vc_pairing_delete_tree.
        minimum (NTP4VCPairingDeleteHeap t) = minimum_tree t) /\
     size_heap (heap_of empty) = (&0:int) /\
     (!e:A. ~((&0:int) < occ_heap e (heap_of empty))))
    ==>
    (&0:int) < size_heap (heap_of hh)
    ==>
    ((?root:A.
      ?children:(A ntp4vc_pairing_delete_tree)list.
        heap_of hh =
          NTP4VCPairingDeleteHeap
            (NTP4VCPairingDeleteTree root children) /\
        heap_list children) /\
     (!result:B.
        (?root:A.
         ?children:(A ntp4vc_pairing_delete_tree)list.
           heap_of hh =
             NTP4VCPairingDeleteHeap
               (NTP4VCPairingDeleteTree root children) /\
           size_heap (heap_of result) = size_list children /\
           (!x:A.
              occ_heap x (heap_of result) = occ_list x children))
        ==>
        occ_heap (minimum (heap_of hh)) (heap_of result) =
          occ_heap (minimum (heap_of hh)) (heap_of hh) - (&1:int) /\
        (!y:A.
           ~(y = minimum (heap_of hh))
           ==> occ_heap y (heap_of result) = occ_heap y (heap_of hh)) /\
        size_heap (heap_of result) =
          size_heap (heap_of hh) - (&1:int)))`;;

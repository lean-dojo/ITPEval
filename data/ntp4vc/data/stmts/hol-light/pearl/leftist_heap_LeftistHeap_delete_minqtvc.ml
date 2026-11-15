(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/leftist_heap_LeftistHeap_delete_minqtvc: a leftist-heap delete-min
  verification condition preserving heap and leftist invariants while
  removing one occurrence of the root minimum and decreasing the size by one.
  This file contains no proof.
*)

let ntp4vc_leftist_delete_tree_INDUCT,
    ntp4vc_leftist_delete_tree_RECURSION =
  define_type
    "ntp4vc_leftist_delete_tree =
       NTP4VCLeftistDeleteEmpty
     | NTP4VCLeftistDeleteNode
         int ntp4vc_leftist_delete_tree A ntp4vc_leftist_delete_tree";;

let ntp4vc_leftist_delete_size =
  new_recursive_definition ntp4vc_leftist_delete_tree_RECURSION
   `(ntp4vc_leftist_delete_size
       (NTP4VCLeftistDeleteEmpty:A ntp4vc_leftist_delete_tree) =
       (&0:int)) /\
    (!s:int.
     !l r:A ntp4vc_leftist_delete_tree.
     !x:A.
       ntp4vc_leftist_delete_size
         (NTP4VCLeftistDeleteNode s l x r) =
       (&1:int) +
       ntp4vc_leftist_delete_size l +
       ntp4vc_leftist_delete_size r)`;;

let ntp4vc_leftist_delete_occ =
  new_recursive_definition ntp4vc_leftist_delete_tree_RECURSION
   `(!x:A.
       ntp4vc_leftist_delete_occ x NTP4VCLeftistDeleteEmpty =
       (&0:int)) /\
    (!x y:A.
     !s:int.
     !l r:A ntp4vc_leftist_delete_tree.
       ntp4vc_leftist_delete_occ x
         (NTP4VCLeftistDeleteNode s l y r) =
       (if x = y then (&1:int) else (&0:int)) +
       ntp4vc_leftist_delete_occ x l +
       ntp4vc_leftist_delete_occ x r)`;;

let ntp4vc_leftist_delete_le_root =
  new_recursive_definition ntp4vc_leftist_delete_tree_RECURSION
   `(!le:A->A->bool.
     !e:A.
       ntp4vc_leftist_delete_le_root
         le e NTP4VCLeftistDeleteEmpty = T) /\
    (!le:A->A->bool.
     !e x:A.
     !s:int.
     !l r:A ntp4vc_leftist_delete_tree.
       ntp4vc_leftist_delete_le_root le e
         (NTP4VCLeftistDeleteNode s l x r) =
       le e x)`;;

let ntp4vc_leftist_delete_is_heap =
  new_recursive_definition ntp4vc_leftist_delete_tree_RECURSION
   `(!le:A->A->bool.
       ntp4vc_leftist_delete_is_heap
         le NTP4VCLeftistDeleteEmpty = T) /\
    (!le:A->A->bool.
     !x:A.
     !s:int.
     !l r:A ntp4vc_leftist_delete_tree.
       ntp4vc_leftist_delete_is_heap le
         (NTP4VCLeftistDeleteNode s l x r) =
       (ntp4vc_leftist_delete_le_root le x l /\
        ntp4vc_leftist_delete_is_heap le l /\
        ntp4vc_leftist_delete_le_root le x r /\
        ntp4vc_leftist_delete_is_heap le r))`;;

let ntp4vc_leftist_delete_int_min = new_definition
  `ntp4vc_leftist_delete_int_min (x:int) (y:int) =
     if x <= y then x else y`;;

let ntp4vc_leftist_delete_rank =
  new_recursive_definition ntp4vc_leftist_delete_tree_RECURSION
   `(ntp4vc_leftist_delete_rank
       (NTP4VCLeftistDeleteEmpty:A ntp4vc_leftist_delete_tree) =
       (&0:int)) /\
    (!s:int.
     !l r:A ntp4vc_leftist_delete_tree.
     !x:A.
       ntp4vc_leftist_delete_rank
         (NTP4VCLeftistDeleteNode s l x r) =
       (&1:int) +
       ntp4vc_leftist_delete_int_min
         (ntp4vc_leftist_delete_rank l)
         (ntp4vc_leftist_delete_rank r))`;;

let ntp4vc_leftist_delete_leftist =
  new_recursive_definition ntp4vc_leftist_delete_tree_RECURSION
   `(ntp4vc_leftist_delete_leftist
       (NTP4VCLeftistDeleteEmpty:A ntp4vc_leftist_delete_tree) = T) /\
    (!s:int.
     !l r:A ntp4vc_leftist_delete_tree.
     !x:A.
       ntp4vc_leftist_delete_leftist
         (NTP4VCLeftistDeleteNode s l x r) =
       (s =
          ntp4vc_leftist_delete_rank
            (NTP4VCLeftistDeleteNode s l x r) /\
        ntp4vc_leftist_delete_leftist l /\
        ntp4vc_leftist_delete_leftist r /\
        ntp4vc_leftist_delete_rank r <=
          ntp4vc_leftist_delete_rank l))`;;

let ntp4vc_leftist_delete_leftist_heap = new_definition
  `ntp4vc_leftist_delete_leftist_heap
     (le:A->A->bool)
     (h:A ntp4vc_leftist_delete_tree) <=>
     ntp4vc_leftist_delete_is_heap le h /\
     ntp4vc_leftist_delete_leftist h`;;

let statement =
 `!le:A->A->bool.
  !minimum:A ntp4vc_leftist_delete_tree->A.
  !h:A ntp4vc_leftist_delete_tree.
    ((!x:A. le x x) /\
     (!x y z:A. le x y /\ le y z ==> le x z) /\
     (!x y:A. le x y \/ le y x) /\
     (!s:int.
      !l r:A ntp4vc_leftist_delete_tree.
      !x:A.
        minimum (NTP4VCLeftistDeleteNode s l x r) = x))
    ==>
    (&0:int) < ntp4vc_leftist_delete_size h
    ==>
    ntp4vc_leftist_delete_leftist_heap le h
    ==>
    ((?s:int.
      ?l r:A ntp4vc_leftist_delete_tree.
      ?x:A.
        h = NTP4VCLeftistDeleteNode s l x r /\
        ntp4vc_leftist_delete_leftist_heap le l /\
        ntp4vc_leftist_delete_leftist_heap le r) /\
     (!result:A ntp4vc_leftist_delete_tree.
        (?s:int.
         ?l r:A ntp4vc_leftist_delete_tree.
         ?x:A.
           h = NTP4VCLeftistDeleteNode s l x r /\
           ntp4vc_leftist_delete_size result =
             ntp4vc_leftist_delete_size l +
             ntp4vc_leftist_delete_size r /\
           (!e:A.
              ntp4vc_leftist_delete_occ e result =
              ntp4vc_leftist_delete_occ e l +
              ntp4vc_leftist_delete_occ e r) /\
           ntp4vc_leftist_delete_leftist_heap le result)
        ==>
        ntp4vc_leftist_delete_occ (minimum h) result =
          ntp4vc_leftist_delete_occ (minimum h) h - (&1:int) /\
        (!e:A.
           ~(e = minimum h)
           ==> ntp4vc_leftist_delete_occ e result =
               ntp4vc_leftist_delete_occ e h) /\
        ntp4vc_leftist_delete_size result =
          ntp4vc_leftist_delete_size h - (&1:int) /\
        ntp4vc_leftist_delete_leftist_heap le result))`;;

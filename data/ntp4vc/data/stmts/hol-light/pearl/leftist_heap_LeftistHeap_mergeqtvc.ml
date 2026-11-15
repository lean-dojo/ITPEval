(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/leftist_heap_LeftistHeap_mergeqtvc: a leftist-heap merge verification
  condition expressing recursive-call obligations and preservation of size,
  element multiplicities, heap order, and leftist invariants. This file
  contains no proof.
*)

let ntp4vc_leftist_merge_tree_INDUCT,
    ntp4vc_leftist_merge_tree_RECURSION =
  define_type
    "ntp4vc_leftist_merge_tree =
       NTP4VCLeftistMergeEmpty
     | NTP4VCLeftistMergeNode
         int ntp4vc_leftist_merge_tree A ntp4vc_leftist_merge_tree";;

let ntp4vc_leftist_merge_size =
  new_recursive_definition ntp4vc_leftist_merge_tree_RECURSION
   `(ntp4vc_leftist_merge_size
       (NTP4VCLeftistMergeEmpty:A ntp4vc_leftist_merge_tree) =
       (&0:int)) /\
    (!s:int.
     !l r:A ntp4vc_leftist_merge_tree.
     !x:A.
       ntp4vc_leftist_merge_size
         (NTP4VCLeftistMergeNode s l x r) =
       (&1:int) +
       ntp4vc_leftist_merge_size l +
       ntp4vc_leftist_merge_size r)`;;

let ntp4vc_leftist_merge_occ =
  new_recursive_definition ntp4vc_leftist_merge_tree_RECURSION
   `(!x:A.
       ntp4vc_leftist_merge_occ x NTP4VCLeftistMergeEmpty =
       (&0:int)) /\
    (!x y:A.
     !s:int.
     !l r:A ntp4vc_leftist_merge_tree.
       ntp4vc_leftist_merge_occ x
         (NTP4VCLeftistMergeNode s l y r) =
       (if x = y then (&1:int) else (&0:int)) +
       ntp4vc_leftist_merge_occ x l +
       ntp4vc_leftist_merge_occ x r)`;;

let ntp4vc_leftist_merge_le_root =
  new_recursive_definition ntp4vc_leftist_merge_tree_RECURSION
   `(!le:A->A->bool.
     !e:A.
       ntp4vc_leftist_merge_le_root
         le e NTP4VCLeftistMergeEmpty = T) /\
    (!le:A->A->bool.
     !e x:A.
     !s:int.
     !l r:A ntp4vc_leftist_merge_tree.
       ntp4vc_leftist_merge_le_root le e
         (NTP4VCLeftistMergeNode s l x r) =
       le e x)`;;

let ntp4vc_leftist_merge_is_heap =
  new_recursive_definition ntp4vc_leftist_merge_tree_RECURSION
   `(!le:A->A->bool.
       ntp4vc_leftist_merge_is_heap
         le NTP4VCLeftistMergeEmpty = T) /\
    (!le:A->A->bool.
     !x:A.
     !s:int.
     !l r:A ntp4vc_leftist_merge_tree.
       ntp4vc_leftist_merge_is_heap le
         (NTP4VCLeftistMergeNode s l x r) =
       (ntp4vc_leftist_merge_le_root le x l /\
        ntp4vc_leftist_merge_is_heap le l /\
        ntp4vc_leftist_merge_le_root le x r /\
        ntp4vc_leftist_merge_is_heap le r))`;;

let ntp4vc_leftist_merge_int_min = new_definition
  `ntp4vc_leftist_merge_int_min (x:int) (y:int) =
     if x <= y then x else y`;;

let ntp4vc_leftist_merge_rank =
  new_recursive_definition ntp4vc_leftist_merge_tree_RECURSION
   `(ntp4vc_leftist_merge_rank
       (NTP4VCLeftistMergeEmpty:A ntp4vc_leftist_merge_tree) =
       (&0:int)) /\
    (!s:int.
     !l r:A ntp4vc_leftist_merge_tree.
     !x:A.
       ntp4vc_leftist_merge_rank
         (NTP4VCLeftistMergeNode s l x r) =
       (&1:int) +
       ntp4vc_leftist_merge_int_min
         (ntp4vc_leftist_merge_rank l)
         (ntp4vc_leftist_merge_rank r))`;;

let ntp4vc_leftist_merge_leftist =
  new_recursive_definition ntp4vc_leftist_merge_tree_RECURSION
   `(ntp4vc_leftist_merge_leftist
       (NTP4VCLeftistMergeEmpty:A ntp4vc_leftist_merge_tree) = T) /\
    (!s:int.
     !l r:A ntp4vc_leftist_merge_tree.
     !x:A.
       ntp4vc_leftist_merge_leftist
         (NTP4VCLeftistMergeNode s l x r) =
       (s =
          ntp4vc_leftist_merge_rank
            (NTP4VCLeftistMergeNode s l x r) /\
        ntp4vc_leftist_merge_leftist l /\
        ntp4vc_leftist_merge_leftist r /\
        ntp4vc_leftist_merge_rank r <=
          ntp4vc_leftist_merge_rank l))`;;

let ntp4vc_leftist_merge_leftist_heap = new_definition
  `ntp4vc_leftist_merge_leftist_heap
     (le:A->A->bool)
     (h:A ntp4vc_leftist_merge_tree) <=>
     ntp4vc_leftist_merge_is_heap le h /\
     ntp4vc_leftist_merge_leftist h`;;

let ntp4vc_leftist_merge_left_ready = new_definition
  `ntp4vc_leftist_merge_left_ready
     (le:A->A->bool)
     (h1:A ntp4vc_leftist_merge_tree)
     (h2:A ntp4vc_leftist_merge_tree)
     (l1:A ntp4vc_leftist_merge_tree)
     (x1:A)
     (r1:A ntp4vc_leftist_merge_tree) <=>
     (((&0:int) <=
         ntp4vc_leftist_merge_size h1 +
         ntp4vc_leftist_merge_size h2 /\
       ntp4vc_leftist_merge_size r1 +
         ntp4vc_leftist_merge_size h2 <
       ntp4vc_leftist_merge_size h1 +
         ntp4vc_leftist_merge_size h2) /\
      ntp4vc_leftist_merge_leftist_heap le r1 /\
      ntp4vc_leftist_merge_leftist_heap le h2) /\
     (!o1:A ntp4vc_leftist_merge_tree.
        ntp4vc_leftist_merge_size o1 =
          ntp4vc_leftist_merge_size r1 +
          ntp4vc_leftist_merge_size h2 /\
        (!x8:A.
           ntp4vc_leftist_merge_occ x8 o1 =
           ntp4vc_leftist_merge_occ x8 r1 +
           ntp4vc_leftist_merge_occ x8 h2) /\
        ntp4vc_leftist_merge_leftist_heap le o1
        ==>
        (ntp4vc_leftist_merge_leftist_heap le o1 /\
         ntp4vc_leftist_merge_leftist_heap le l1) /\
        ntp4vc_leftist_merge_le_root le x1 l1 /\
        ntp4vc_leftist_merge_le_root le x1 o1)`;;

let ntp4vc_leftist_merge_right_ready = new_definition
  `ntp4vc_leftist_merge_right_ready
     (le:A->A->bool)
     (h1:A ntp4vc_leftist_merge_tree)
     (h2:A ntp4vc_leftist_merge_tree)
     (l2:A ntp4vc_leftist_merge_tree)
     (x2:A)
     (r2:A ntp4vc_leftist_merge_tree) <=>
     (((&0:int) <=
         ntp4vc_leftist_merge_size h1 +
         ntp4vc_leftist_merge_size h2 /\
       ntp4vc_leftist_merge_size h1 +
         ntp4vc_leftist_merge_size r2 <
       ntp4vc_leftist_merge_size h1 +
         ntp4vc_leftist_merge_size h2) /\
      ntp4vc_leftist_merge_leftist_heap le h1 /\
      ntp4vc_leftist_merge_leftist_heap le r2) /\
     (!o1:A ntp4vc_leftist_merge_tree.
        ntp4vc_leftist_merge_size o1 =
          ntp4vc_leftist_merge_size h1 +
          ntp4vc_leftist_merge_size r2 /\
        (!x8:A.
           ntp4vc_leftist_merge_occ x8 o1 =
           ntp4vc_leftist_merge_occ x8 h1 +
           ntp4vc_leftist_merge_occ x8 r2) /\
        ntp4vc_leftist_merge_leftist_heap le o1
        ==>
        (ntp4vc_leftist_merge_leftist_heap le o1 /\
         ntp4vc_leftist_merge_leftist_heap le l2) /\
        ntp4vc_leftist_merge_le_root le x2 l2 /\
        ntp4vc_leftist_merge_le_root le x2 o1)`;;

let ntp4vc_leftist_merge_ready = new_definition
  `ntp4vc_leftist_merge_ready
     (le:A->A->bool)
     (h1:A ntp4vc_leftist_merge_tree)
     (h2:A ntp4vc_leftist_merge_tree) <=>
     h2 = NTP4VCLeftistMergeEmpty \/
     (?s2:int.
      ?l2 r2:A ntp4vc_leftist_merge_tree.
      ?x2:A.
        h2 = NTP4VCLeftistMergeNode s2 l2 x2 r2 /\
        (h1 = NTP4VCLeftistMergeEmpty \/
         (?s1:int.
          ?l1 r1:A ntp4vc_leftist_merge_tree.
          ?x1:A.
            h1 = NTP4VCLeftistMergeNode s1 l1 x1 r1 /\
            (if le x1 x2 then
               ntp4vc_leftist_merge_left_ready
                 le h1 h2 l1 x1 r1
             else
               ntp4vc_leftist_merge_right_ready
                 le h1 h2 l2 x2 r2))))`;;

let ntp4vc_leftist_merge_left_step = new_definition
  `ntp4vc_leftist_merge_left_step
     (le:A->A->bool)
     (minimum:A ntp4vc_leftist_merge_tree->A)
     (h2:A ntp4vc_leftist_merge_tree)
     (l1:A ntp4vc_leftist_merge_tree)
     (x1:A)
     (r1:A ntp4vc_leftist_merge_tree)
     (result:A ntp4vc_leftist_merge_tree) <=>
     (?o1:A ntp4vc_leftist_merge_tree.
        (ntp4vc_leftist_merge_size o1 =
           ntp4vc_leftist_merge_size r1 +
           ntp4vc_leftist_merge_size h2 /\
         (!x8:A.
            ntp4vc_leftist_merge_occ x8 o1 =
            ntp4vc_leftist_merge_occ x8 r1 +
            ntp4vc_leftist_merge_occ x8 h2) /\
         ntp4vc_leftist_merge_leftist_heap le o1) /\
        ntp4vc_leftist_merge_leftist_heap le result /\
        minimum result = x1 /\
        ntp4vc_leftist_merge_size result =
          (&1:int) +
          ntp4vc_leftist_merge_size l1 +
          ntp4vc_leftist_merge_size o1 /\
        ntp4vc_leftist_merge_occ x1 result =
          (&1:int) +
          ntp4vc_leftist_merge_occ x1 l1 +
          ntp4vc_leftist_merge_occ x1 o1 /\
        (!y:A.
           ~(x1 = y)
           ==> ntp4vc_leftist_merge_occ y result =
               ntp4vc_leftist_merge_occ y l1 +
               ntp4vc_leftist_merge_occ y o1))`;;

let ntp4vc_leftist_merge_right_step = new_definition
  `ntp4vc_leftist_merge_right_step
     (le:A->A->bool)
     (minimum:A ntp4vc_leftist_merge_tree->A)
     (h1:A ntp4vc_leftist_merge_tree)
     (l2:A ntp4vc_leftist_merge_tree)
     (x2:A)
     (r2:A ntp4vc_leftist_merge_tree)
     (result:A ntp4vc_leftist_merge_tree) <=>
     (?o1:A ntp4vc_leftist_merge_tree.
        (ntp4vc_leftist_merge_size o1 =
           ntp4vc_leftist_merge_size h1 +
           ntp4vc_leftist_merge_size r2 /\
         (!x8:A.
            ntp4vc_leftist_merge_occ x8 o1 =
            ntp4vc_leftist_merge_occ x8 h1 +
            ntp4vc_leftist_merge_occ x8 r2) /\
         ntp4vc_leftist_merge_leftist_heap le o1) /\
        ntp4vc_leftist_merge_leftist_heap le result /\
        minimum result = x2 /\
        ntp4vc_leftist_merge_size result =
          (&1:int) +
          ntp4vc_leftist_merge_size l2 +
          ntp4vc_leftist_merge_size o1 /\
        ntp4vc_leftist_merge_occ x2 result =
          (&1:int) +
          ntp4vc_leftist_merge_occ x2 l2 +
          ntp4vc_leftist_merge_occ x2 o1 /\
        (!y:A.
           ~(x2 = y)
           ==> ntp4vc_leftist_merge_occ y result =
               ntp4vc_leftist_merge_occ y l2 +
               ntp4vc_leftist_merge_occ y o1))`;;

let ntp4vc_leftist_merge_step = new_definition
  `ntp4vc_leftist_merge_step
     (le:A->A->bool)
     (minimum:A ntp4vc_leftist_merge_tree->A)
     (h1:A ntp4vc_leftist_merge_tree)
     (h2:A ntp4vc_leftist_merge_tree)
     (result:A ntp4vc_leftist_merge_tree) <=>
     (h2 = NTP4VCLeftistMergeEmpty /\ result = h1) \/
     (?s2:int.
      ?l2 r2:A ntp4vc_leftist_merge_tree.
      ?x2:A.
        h2 = NTP4VCLeftistMergeNode s2 l2 x2 r2 /\
        ((h1 = NTP4VCLeftistMergeEmpty /\ result = h2) \/
         (?s1:int.
          ?l1 r1:A ntp4vc_leftist_merge_tree.
          ?x1:A.
            h1 = NTP4VCLeftistMergeNode s1 l1 x1 r1 /\
            (if le x1 x2 then
               ntp4vc_leftist_merge_left_step
                 le minimum h2 l1 x1 r1 result
             else
               ntp4vc_leftist_merge_right_step
                 le minimum h1 l2 x2 r2 result))))`;;

let statement =
  `!le:A->A->bool.
   !minimum:A ntp4vc_leftist_merge_tree->A.
   !h1 h2:A ntp4vc_leftist_merge_tree.
     ((!x:A. le x x) /\
      (!x y z:A. le x y /\ le y z ==> le x z) /\
      (!x y:A. le x y \/ le y x) /\
      (!s:int.
       !l r:A ntp4vc_leftist_merge_tree.
       !x:A.
         minimum (NTP4VCLeftistMergeNode s l x r) = x))
     ==>
     ntp4vc_leftist_merge_leftist_heap le h1
     ==>
     ntp4vc_leftist_merge_leftist_heap le h2
     ==>
     ntp4vc_leftist_merge_ready le h1 h2 /\
     (!result:A ntp4vc_leftist_merge_tree.
        ntp4vc_leftist_merge_step le minimum h1 h2 result
        ==>
        ntp4vc_leftist_merge_size result =
          ntp4vc_leftist_merge_size h1 +
          ntp4vc_leftist_merge_size h2 /\
        (!x:A.
           ntp4vc_leftist_merge_occ x result =
           ntp4vc_leftist_merge_occ x h1 +
           ntp4vc_leftist_merge_occ x h2) /\
        ntp4vc_leftist_merge_leftist_heap le result)`;;

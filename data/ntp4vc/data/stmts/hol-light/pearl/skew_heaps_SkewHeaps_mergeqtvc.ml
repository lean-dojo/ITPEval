(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/skew_heaps_SkewHeaps_mergeqtvc: the skew-heap merge verification
  condition expressing recursive-call obligations and preservation of heap
  order, element multiplicities, and tree size. This file contains no proof.
*)

let ntp4vc_skew_merge_tree_INDUCT,
    ntp4vc_skew_merge_tree_RECURSION =
  define_type
    "ntp4vc_skew_merge_tree =
       NTP4VCSkewMergeEmpty
     | NTP4VCSkewMergeNode
         ntp4vc_skew_merge_tree A ntp4vc_skew_merge_tree";;

let ntp4vc_skew_merge_size =
  new_recursive_definition ntp4vc_skew_merge_tree_RECURSION
   `(ntp4vc_skew_merge_size
       (NTP4VCSkewMergeEmpty:A ntp4vc_skew_merge_tree) =
       (&0:int)) /\
    (!l r:A ntp4vc_skew_merge_tree.
     !x:A.
       ntp4vc_skew_merge_size
         (NTP4VCSkewMergeNode l x r) =
       (&1:int) +
       ntp4vc_skew_merge_size l +
       ntp4vc_skew_merge_size r)`;;

let ntp4vc_skew_merge_occ =
  new_recursive_definition ntp4vc_skew_merge_tree_RECURSION
   `(!x:A.
       ntp4vc_skew_merge_occ x NTP4VCSkewMergeEmpty =
       (&0:int)) /\
    (!x y:A.
     !l r:A ntp4vc_skew_merge_tree.
       ntp4vc_skew_merge_occ x
         (NTP4VCSkewMergeNode l y r) =
       (if y = x then (&1:int) else (&0:int)) +
       ntp4vc_skew_merge_occ x l +
       ntp4vc_skew_merge_occ x r)`;;

let ntp4vc_skew_merge_le_root =
  new_recursive_definition ntp4vc_skew_merge_tree_RECURSION
   `(!le:A->A->bool.
     !e:A.
       ntp4vc_skew_merge_le_root
         le e NTP4VCSkewMergeEmpty = T) /\
    (!le:A->A->bool.
     !e x:A.
     !l r:A ntp4vc_skew_merge_tree.
       ntp4vc_skew_merge_le_root le e
         (NTP4VCSkewMergeNode l x r) =
       le e x)`;;

let ntp4vc_skew_merge_heap =
  new_recursive_definition ntp4vc_skew_merge_tree_RECURSION
   `(!le:A->A->bool.
       ntp4vc_skew_merge_heap le NTP4VCSkewMergeEmpty = T) /\
    (!le:A->A->bool.
     !x:A.
     !l r:A ntp4vc_skew_merge_tree.
       ntp4vc_skew_merge_heap le
         (NTP4VCSkewMergeNode l x r) =
       (ntp4vc_skew_merge_le_root le x l /\
        ntp4vc_skew_merge_heap le l /\
        ntp4vc_skew_merge_le_root le x r /\
        ntp4vc_skew_merge_heap le r))`;;

let ntp4vc_skew_merge_ready = new_definition
  `ntp4vc_skew_merge_ready
     (le:A->A->bool)
     (t1:A ntp4vc_skew_merge_tree)
     (t2:A ntp4vc_skew_merge_tree) <=>
     t2 = NTP4VCSkewMergeEmpty \/
     (?l2 r2:A ntp4vc_skew_merge_tree.
      ?x2:A.
        t2 = NTP4VCSkewMergeNode l2 x2 r2 /\
        (t1 = NTP4VCSkewMergeEmpty \/
         (?l1 r1:A ntp4vc_skew_merge_tree.
          ?x1:A.
            t1 = NTP4VCSkewMergeNode l1 x1 r1 /\
            (if le x1 x2 then
               (((&0:int) <=
                   ntp4vc_skew_merge_size t1 +
                   ntp4vc_skew_merge_size t2 /\
                 ntp4vc_skew_merge_size r1 +
                   ntp4vc_skew_merge_size t2 <
                 ntp4vc_skew_merge_size t1 +
                   ntp4vc_skew_merge_size t2) /\
                ntp4vc_skew_merge_heap le r1 /\
                ntp4vc_skew_merge_heap le t2)
             else
               (((&0:int) <=
                   ntp4vc_skew_merge_size t1 +
                   ntp4vc_skew_merge_size t2 /\
                 ntp4vc_skew_merge_size r2 +
                   ntp4vc_skew_merge_size t1 <
                 ntp4vc_skew_merge_size t1 +
                   ntp4vc_skew_merge_size t2) /\
                ntp4vc_skew_merge_heap le r2 /\
                ntp4vc_skew_merge_heap le t1)))))`;;

let ntp4vc_skew_merge_step = new_definition
  `ntp4vc_skew_merge_step
     (le:A->A->bool)
     (t1:A ntp4vc_skew_merge_tree)
     (t2:A ntp4vc_skew_merge_tree)
     (result:A ntp4vc_skew_merge_tree) <=>
     (t2 = NTP4VCSkewMergeEmpty /\
      ((t1 = NTP4VCSkewMergeEmpty /\ result = t2) \/
       (?l1 r1:A ntp4vc_skew_merge_tree.
        ?x1:A.
          t1 = NTP4VCSkewMergeNode l1 x1 r1 /\
          result = t1))) \/
     (?l2 r2:A ntp4vc_skew_merge_tree.
      ?x2:A.
        t2 = NTP4VCSkewMergeNode l2 x2 r2 /\
        ((t1 = NTP4VCSkewMergeEmpty /\ result = t2) \/
         (?l1 r1:A ntp4vc_skew_merge_tree.
          ?x1:A.
            t1 = NTP4VCSkewMergeNode l1 x1 r1 /\
            (if le x1 x2 then
               ?o1:A ntp4vc_skew_merge_tree.
                 (ntp4vc_skew_merge_heap le o1 /\
                  (!e:A.
                     ntp4vc_skew_merge_occ e o1 =
                     ntp4vc_skew_merge_occ e r1 +
                     ntp4vc_skew_merge_occ e t2) /\
                  ntp4vc_skew_merge_size o1 =
                    ntp4vc_skew_merge_size r1 +
                    ntp4vc_skew_merge_size t2) /\
                 result = NTP4VCSkewMergeNode o1 x1 l1
             else
               ?o1:A ntp4vc_skew_merge_tree.
                 (ntp4vc_skew_merge_heap le o1 /\
                  (!e:A.
                     ntp4vc_skew_merge_occ e o1 =
                     ntp4vc_skew_merge_occ e r2 +
                     ntp4vc_skew_merge_occ e t1) /\
                  ntp4vc_skew_merge_size o1 =
                    ntp4vc_skew_merge_size r2 +
                    ntp4vc_skew_merge_size t1) /\
                 result = NTP4VCSkewMergeNode o1 x2 l2))))`;;

let statement =
  `!le:A->A->bool.
   !t1 t2:A ntp4vc_skew_merge_tree.
     ((!x:A. le x x) /\
      (!x y z:A. le x y /\ le y z ==> le x z) /\
      (!x y:A. le x y \/ le y x))
     ==>
     ntp4vc_skew_merge_heap le t1
     ==>
     ntp4vc_skew_merge_heap le t2
     ==>
     ntp4vc_skew_merge_ready le t1 t2 /\
     (!result:A ntp4vc_skew_merge_tree.
        ntp4vc_skew_merge_step le t1 t2 result
        ==>
        ntp4vc_skew_merge_heap le result /\
        (!e:A.
           ntp4vc_skew_merge_occ e result =
           ntp4vc_skew_merge_occ e t1 +
           ntp4vc_skew_merge_occ e t2) /\
        ntp4vc_skew_merge_size result =
          ntp4vc_skew_merge_size t1 +
          ntp4vc_skew_merge_size t2)`;;

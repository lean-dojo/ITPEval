(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/skew_heaps_HeapSort_heapsortqtvc: the skew-heap heapsort verification
  condition for the heap-building and extraction loops, preserving heap order,
  element multiplicities, sorted prefixes, and whole-array permutation. This
  file contains no proof.
*)

let ntp4vc_skew_heapsort_tree_INDUCT,
    ntp4vc_skew_heapsort_tree_RECURSION =
  define_type
    "ntp4vc_skew_heapsort_tree =
       NTP4VCSkewHeapsortEmpty
     | NTP4VCSkewHeapsortNode
         ntp4vc_skew_heapsort_tree A ntp4vc_skew_heapsort_tree";;

let ntp4vc_skew_heapsort_size =
  new_recursive_definition ntp4vc_skew_heapsort_tree_RECURSION
   `(ntp4vc_skew_heapsort_size
       (NTP4VCSkewHeapsortEmpty:A ntp4vc_skew_heapsort_tree) =
       (&0:int)) /\
    (!l r:A ntp4vc_skew_heapsort_tree.
     !x:A.
       ntp4vc_skew_heapsort_size
         (NTP4VCSkewHeapsortNode l x r) =
       (&1:int) +
       ntp4vc_skew_heapsort_size l +
       ntp4vc_skew_heapsort_size r)`;;

let ntp4vc_skew_heapsort_occ =
  new_recursive_definition ntp4vc_skew_heapsort_tree_RECURSION
   `(!x:A.
       ntp4vc_skew_heapsort_occ x NTP4VCSkewHeapsortEmpty =
       (&0:int)) /\
    (!x y:A.
     !l r:A ntp4vc_skew_heapsort_tree.
       ntp4vc_skew_heapsort_occ x
         (NTP4VCSkewHeapsortNode l y r) =
       (if y = x then (&1:int) else (&0:int)) +
       ntp4vc_skew_heapsort_occ x l +
       ntp4vc_skew_heapsort_occ x r)`;;

let ntp4vc_skew_heapsort_mem = new_definition
  `ntp4vc_skew_heapsort_mem
     (x:A) (t:A ntp4vc_skew_heapsort_tree) <=>
     (&0:int) < ntp4vc_skew_heapsort_occ x t`;;

let ntp4vc_skew_heapsort_le_root =
  new_recursive_definition ntp4vc_skew_heapsort_tree_RECURSION
   `(!le:A->A->bool.
     !e:A.
       ntp4vc_skew_heapsort_le_root
         le e NTP4VCSkewHeapsortEmpty = T) /\
    (!le:A->A->bool.
     !e x:A.
     !l r:A ntp4vc_skew_heapsort_tree.
       ntp4vc_skew_heapsort_le_root le e
         (NTP4VCSkewHeapsortNode l x r) =
       le e x)`;;

let ntp4vc_skew_heapsort_heap =
  new_recursive_definition ntp4vc_skew_heapsort_tree_RECURSION
   `(!le:A->A->bool.
       ntp4vc_skew_heapsort_heap
         le NTP4VCSkewHeapsortEmpty = T) /\
    (!le:A->A->bool.
     !x:A.
     !l r:A ntp4vc_skew_heapsort_tree.
       ntp4vc_skew_heapsort_heap le
         (NTP4VCSkewHeapsortNode l x r) =
       (ntp4vc_skew_heapsort_le_root le x l /\
        ntp4vc_skew_heapsort_heap le l /\
        ntp4vc_skew_heapsort_le_root le x r /\
        ntp4vc_skew_heapsort_heap le r))`;;

let ntp4vc_skew_heapsort_index = new_definition
  `ntp4vc_skew_heapsort_index (i:int) =
     if i < (&0:int) then 0 else num_of_int i`;;

let ntp4vc_skew_heapsort_nth = new_definition
  `ntp4vc_skew_heapsort_nth (a:A list) (i:int) =
     if ntp4vc_skew_heapsort_index i < LENGTH a then
       EL (ntp4vc_skew_heapsort_index i) a
     else
       (ARB:A)`;;

let ntp4vc_skew_heapsort_update =
  new_recursive_definition list_RECURSION
   `(!n:num.
     !x:A.
       ntp4vc_skew_heapsort_update ([]:A list) n x = []) /\
    (!h:A.
     !t:A list.
     !n:num.
     !x:A.
       ntp4vc_skew_heapsort_update (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h
         (ntp4vc_skew_heapsort_update t (PRE n) x))`;;

let ntp4vc_skew_heapsort_map_occ = new_definition
  `ntp4vc_skew_heapsort_map_occ
     (x:A) (a:A list) (l:int) (u:int) =
     (&(CARD
        {i:int |
           l <= i /\ i < u /\
           ntp4vc_skew_heapsort_nth a i = x}):int)`;;

let ntp4vc_skew_heapsort_sorted_sub = new_definition
  `ntp4vc_skew_heapsort_sorted_sub
     (le:A->A->bool) (a:A list) (l:int) (u:int) <=>
     !i1 i2:int.
       l <= i1 /\ i1 < i2 /\ i2 < u
       ==> le
         (ntp4vc_skew_heapsort_nth a i1)
         (ntp4vc_skew_heapsort_nth a i2)`;;

let ntp4vc_skew_heapsort_sorted = new_definition
  `ntp4vc_skew_heapsort_sorted
     (le:A->A->bool) (a:A list) <=>
     !i1 i2:int.
       (&0:int) <= i1 /\ i1 < i2 /\
       i2 < (&(LENGTH a):int)
       ==> le
         (ntp4vc_skew_heapsort_nth a i1)
         (ntp4vc_skew_heapsort_nth a i2)`;;

let ntp4vc_skew_heapsort_permut = new_definition
  `ntp4vc_skew_heapsort_permut (a:A list) (b:A list) <=>
     LENGTH a = LENGTH b /\
     !x:A.
       CARD {i:num | i < LENGTH a /\ EL i a = x} =
       CARD {i:num | i < LENGTH b /\ EL i b = x}`;;

let ntp4vc_skew_heapsort_extraction = new_definition
 `ntp4vc_skew_heapsort_extraction
    (le:A->A->bool)
    (minimum:A ntp4vc_skew_heapsort_tree->A)
    (a:A list)
    (t:A ntp4vc_skew_heapsort_tree) <=>
    let n = (&(LENGTH a):int) in
    let o2 = n - (&1:int) in
    (((&0:int) <= o2 + (&1:int)
      ==>
      (ntp4vc_skew_heapsort_sorted_sub
         le a (&0:int) (&0:int) /\
       (ntp4vc_skew_heapsort_heap le t /\
        ntp4vc_skew_heapsort_size t = n - (&0:int)) /\
       (!j:int.
          (&0:int) <= j /\ j < (&0:int)
          ==> !e:A.
                ntp4vc_skew_heapsort_mem e t
                ==> le (ntp4vc_skew_heapsort_nth a j) e) /\
       (!e:A.
          ntp4vc_skew_heapsort_map_occ
            e a (&0:int) (&0:int) +
          ntp4vc_skew_heapsort_occ e t =
          ntp4vc_skew_heapsort_map_occ e a (&0:int) n)) /\
      (!t1:A ntp4vc_skew_heapsort_tree.
       !a1:A list.
         LENGTH a1 = LENGTH a
         ==>
         ((!i:int.
             (((&0:int) <= i /\ i <= o2) /\
              ntp4vc_skew_heapsort_sorted_sub
                le a1 (&0:int) i /\
              (ntp4vc_skew_heapsort_heap le t1 /\
               ntp4vc_skew_heapsort_size t1 = n - i) /\
              (!j:int.
                 (&0:int) <= j /\ j < i
                 ==> !e:A.
                       ntp4vc_skew_heapsort_mem e t1
                       ==> le
                         (ntp4vc_skew_heapsort_nth a1 j) e) /\
              (!e:A.
                 ntp4vc_skew_heapsort_map_occ
                   e a1 (&0:int) i +
                 ntp4vc_skew_heapsort_occ e t1 =
                 ntp4vc_skew_heapsort_map_occ
                   e a (&0:int) n))
             ==>
             (ntp4vc_skew_heapsort_heap le t1 /\
              (&0:int) < ntp4vc_skew_heapsort_size t1) /\
             (let o3 = minimum t1 in
              ((&0:int) <= i /\ i < (&(LENGTH a1):int)) /\
              (LENGTH
                 (ntp4vc_skew_heapsort_update
                    a1 (ntp4vc_skew_heapsort_index i) o3) =
               LENGTH a1
               ==>
               (!r:int.
                  (&0:int) <= r /\ r < (&(LENGTH a1):int)
                  ==>
                  ntp4vc_skew_heapsort_nth
                    (ntp4vc_skew_heapsort_update
                       a1 (ntp4vc_skew_heapsort_index i) o3) r =
                  if r = i then o3
                  else ntp4vc_skew_heapsort_nth a1 r)
               ==>
               (ntp4vc_skew_heapsort_heap le t1 /\
                (&0:int) < ntp4vc_skew_heapsort_size t1) /\
               (!o4:A ntp4vc_skew_heapsort_tree.
                  ntp4vc_skew_heapsort_heap le o4 /\
                  ntp4vc_skew_heapsort_occ (minimum t1) o4 =
                    ntp4vc_skew_heapsort_occ (minimum t1) t1 -
                    (&1:int) /\
                  (!e:A.
                     ~(e = minimum t1)
                     ==> ntp4vc_skew_heapsort_occ e o4 =
                         ntp4vc_skew_heapsort_occ e t1) /\
                  ntp4vc_skew_heapsort_size o4 =
                    ntp4vc_skew_heapsort_size t1 - (&1:int)
                  ==>
                  ntp4vc_skew_heapsort_sorted_sub
                    le
                    (ntp4vc_skew_heapsort_update
                       a1 (ntp4vc_skew_heapsort_index i) o3)
                    (&0:int) (i + (&1:int)) /\
                  (ntp4vc_skew_heapsort_heap le o4 /\
                   ntp4vc_skew_heapsort_size o4 =
                     n - (i + (&1:int))) /\
                  (!j:int.
                     (&0:int) <= j /\ j < i + (&1:int)
                     ==> !e:A.
                           ntp4vc_skew_heapsort_mem e o4
                           ==> le
                             (ntp4vc_skew_heapsort_nth
                               (ntp4vc_skew_heapsort_update
                                  a1
                                  (ntp4vc_skew_heapsort_index i)
                                  o3) j)
                             e) /\
                  (!e:A.
                     ntp4vc_skew_heapsort_map_occ
                       e
                       (ntp4vc_skew_heapsort_update
                          a1 (ntp4vc_skew_heapsort_index i) o3)
                       (&0:int) (i + (&1:int)) +
                     ntp4vc_skew_heapsort_occ e o4 =
                     ntp4vc_skew_heapsort_map_occ
                       e a (&0:int) n)))))
          /\
          (ntp4vc_skew_heapsort_sorted_sub
             le a1 (&0:int) (o2 + (&1:int)) /\
           (ntp4vc_skew_heapsort_heap le t1 /\
            ntp4vc_skew_heapsort_size t1 =
              n - (o2 + (&1:int))) /\
           (!j:int.
              (&0:int) <= j /\ j < o2 + (&1:int)
              ==> !e:A.
                    ntp4vc_skew_heapsort_mem e t1
                    ==> le (ntp4vc_skew_heapsort_nth a1 j) e) /\
           (!e:A.
              ntp4vc_skew_heapsort_map_occ
                e a1 (&0:int) (o2 + (&1:int)) +
              ntp4vc_skew_heapsort_occ e t1 =
              ntp4vc_skew_heapsort_map_occ e a (&0:int) n)
           ==>
           ntp4vc_skew_heapsort_sorted le a1 /\
           ntp4vc_skew_heapsort_permut a a1))))
     /\
     (o2 + (&1:int) < (&0:int)
      ==>
      ntp4vc_skew_heapsort_sorted le a /\
      ntp4vc_skew_heapsort_permut a a))`;;

let statement =
 `!le:A->A->bool.
  !minimum:A ntp4vc_skew_heapsort_tree->A.
  !a:A list.
    ((!x:A. le x x) /\
     (!x y z:A. le x y /\ le y z ==> le x z) /\
     (!x y:A. le x y \/ le y x) /\
     (!l r:A ntp4vc_skew_heapsort_tree.
      !x:A.
        minimum (NTP4VCSkewHeapsortNode l x r) = x))
    ==>
    let n = (&(LENGTH a):int) in
    let o1 = n - (&1:int) in
    (((&0:int) <= o1 + (&1:int)
      ==>
      ((ntp4vc_skew_heapsort_heap
          le
          (NTP4VCSkewHeapsortEmpty:
            A ntp4vc_skew_heapsort_tree) /\
        ntp4vc_skew_heapsort_size
          (NTP4VCSkewHeapsortEmpty:
            A ntp4vc_skew_heapsort_tree) =
          (&0:int)) /\
       (!e:A.
          ntp4vc_skew_heapsort_map_occ e a (&0:int) n +
          ntp4vc_skew_heapsort_occ
            e
            (NTP4VCSkewHeapsortEmpty:
              A ntp4vc_skew_heapsort_tree) =
          ntp4vc_skew_heapsort_map_occ e a (&0:int) n)) /\
      (!t:A ntp4vc_skew_heapsort_tree.
         (((( &0:int) <= ntp4vc_skew_heapsort_size t /\
             ntp4vc_skew_heapsort_size t <= o1) /\
            ntp4vc_skew_heapsort_heap le t /\
            (!e:A.
               ntp4vc_skew_heapsort_map_occ
                 e a (ntp4vc_skew_heapsort_size t) n +
               ntp4vc_skew_heapsort_occ e t =
               ntp4vc_skew_heapsort_map_occ e a (&0:int) n))
           ==>
           ((&0:int) <= ntp4vc_skew_heapsort_size t /\
            ntp4vc_skew_heapsort_size t < (&(LENGTH a):int)) /\
           (let o2 =
              ntp4vc_skew_heapsort_nth
                a (ntp4vc_skew_heapsort_size t) in
            ntp4vc_skew_heapsort_heap le t /\
            !o3:A ntp4vc_skew_heapsort_tree.
              ntp4vc_skew_heapsort_heap le o3 /\
              ntp4vc_skew_heapsort_occ o2 o3 =
                ntp4vc_skew_heapsort_occ o2 t + (&1:int) /\
              (!e:A.
                 ~(e = o2)
                 ==> ntp4vc_skew_heapsort_occ e o3 =
                     ntp4vc_skew_heapsort_occ e t) /\
              ntp4vc_skew_heapsort_size o3 =
                ntp4vc_skew_heapsort_size t + (&1:int)
              ==>
              (ntp4vc_skew_heapsort_heap le o3 /\
               ntp4vc_skew_heapsort_size o3 =
                 ntp4vc_skew_heapsort_size t + (&1:int)) /\
              (!e:A.
                 ntp4vc_skew_heapsort_map_occ
                   e a
                   (ntp4vc_skew_heapsort_size t + (&1:int)) n +
                 ntp4vc_skew_heapsort_occ e o3 =
                 ntp4vc_skew_heapsort_map_occ
                   e a (&0:int) n)))
          /\
          ((ntp4vc_skew_heapsort_heap le t /\
            ntp4vc_skew_heapsort_size t = o1 + (&1:int)) /\
           (!e:A.
              ntp4vc_skew_heapsort_map_occ
                e a (o1 + (&1:int)) n +
              ntp4vc_skew_heapsort_occ e t =
              ntp4vc_skew_heapsort_map_occ e a (&0:int) n)
           ==>
           ntp4vc_skew_heapsort_extraction le minimum a t)))
     /\
     (o1 + (&1:int) < (&0:int)
      ==>
      ntp4vc_skew_heapsort_extraction
        le minimum a
        (NTP4VCSkewHeapsortEmpty:
          A ntp4vc_skew_heapsort_tree)))`;;

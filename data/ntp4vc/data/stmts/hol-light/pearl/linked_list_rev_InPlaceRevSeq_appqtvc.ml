(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/linked_list_rev_InPlaceRevSeq_appqtvc: the in-place linked-list
  reversal-and-append verification condition, expressed through disjoint
  list segments and a functional update of the next-pointer map. This file
  contains no proof.
*)

let ntp4vc_linked_list_rev_int_index = new_definition
 `ntp4vc_linked_list_rev_int_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ntp4vc_linked_list_rev_nth = new_definition
 `ntp4vc_linked_list_rev_nth (xs:A list) (i:int) =
    if ntp4vc_linked_list_rev_int_index i < LENGTH xs
    then EL (ntp4vc_linked_list_rev_int_index i) xs
    else ARB`;;

let ntp4vc_linked_list_rev_disjoint = new_definition
 `ntp4vc_linked_list_rev_disjoint (s1:A list) (s2:A list) <=>
    !i1:int.
      (&0:int) <= i1 /\ i1 < (&(LENGTH s1):int)
      ==>
      !i2:int.
        (&0:int) <= i2 /\ i2 < (&(LENGTH s2):int)
        ==>
        ~(ntp4vc_linked_list_rev_nth s1 i1 =
          ntp4vc_linked_list_rev_nth s2 i2)`;;

let ntp4vc_linked_list_rev_list_seg = new_definition
 `ntp4vc_linked_list_rev_list_seg
    (null:A) (next1:A->A) (p:A) (s:A list) (q:A) <=>
    let n = (&(LENGTH s):int) in
    (!i:int.
       (&0:int) <= i /\ i < n
       ==> ~(ntp4vc_linked_list_rev_nth s i = null)) /\
    ((p = q /\ n = (&0:int)) \/
     ((&1:int) <= n /\
      ntp4vc_linked_list_rev_nth s (&0:int) = p /\
      next1 (ntp4vc_linked_list_rev_nth s (n - (&1:int))) = q /\
      (!i:int.
         (&0:int) <= i /\ i < n - (&1:int)
         ==>
         next1 (ntp4vc_linked_list_rev_nth s i) =
         ntp4vc_linked_list_rev_nth s (i + (&1:int)))))`;;

let ntp4vc_linked_list_rev_function_update = new_definition
 `ntp4vc_linked_list_rev_function_update
    (f:A->A) (x:A) (y:A) =
    \z:A. if z = x then y else f z`;;

let statement =
 `!null:A.
  !eq_loc:A->A->bool.
  !next1:A->A.
  !l1:A.
  !l1M:A list.
  !l2:A.
  !l2M:A list.
    (!x y:A. (eq_loc x y = T <=> x = y))
    ==>
    ntp4vc_linked_list_rev_list_seg null next1 l1 l1M null
    ==>
    ntp4vc_linked_list_rev_list_seg null next1 l2 l2M null
    ==>
    ntp4vc_linked_list_rev_disjoint l1M l2M
    ==>
    let o1 = null in
    let o2 = eq_loc l1 o1 in
    (o2 = T <=> l1 = o1)
    ==>
    if o2 = T then
      ntp4vc_linked_list_rev_list_seg
        null next1 l2 (APPEND l1M l2M) null
    else
      (~(l1 = null) /\
       ntp4vc_linked_list_rev_list_seg null next1 l1 [] l1 /\
       ntp4vc_linked_list_rev_list_seg null next1 l1 l1M null /\
       APPEND [] l1M = l1M /\
       ntp4vc_linked_list_rev_disjoint [] l1M) /\
      (!l1pM:A list.
       !pM:A list.
       !p:A.
         ~(p = null) /\
         ntp4vc_linked_list_rev_list_seg null next1 l1 l1pM p /\
         ntp4vc_linked_list_rev_list_seg null next1 p pM null /\
         APPEND l1pM pM = l1M /\
         ntp4vc_linked_list_rev_disjoint l1pM pM
         ==>
         let o3 = null in
         ~(p = null) /\
         let o4 = next1 p in
         let o5 = eq_loc o4 o3 in
         (o5 = T <=> o4 = o3)
         ==>
         if ~(o5 = T) then
           ((&0:int) <= (&1:int) /\
            (&1:int) <= (&(LENGTH pM):int)) /\
           (let o6 = ([]:A list) in
            let o7 = CONS p o6 in
            (&(LENGTH o7):int) =
              (&1:int) + (&(LENGTH o6):int) /\
            ntp4vc_linked_list_rev_nth o7 (&0:int) = p /\
            (!i:int.
               (&0:int) < i /\ i <= (&(LENGTH o6):int)
               ==>
               ntp4vc_linked_list_rev_nth o7 i =
               ntp4vc_linked_list_rev_nth o6 (i - (&1:int)))
            ==>
            let o8 = APPEND l1pM o7 in
            (&(LENGTH o8):int) =
              (&(LENGTH l1pM):int) + (&(LENGTH o7):int) /\
            (!i:int.
               (&0:int) <= i /\ i < (&(LENGTH l1pM):int)
               ==>
               ntp4vc_linked_list_rev_nth o8 i =
               ntp4vc_linked_list_rev_nth l1pM i) /\
            (!i:int.
               (&(LENGTH l1pM):int) <= i /\
               i < (&(LENGTH o8):int)
               ==>
               ntp4vc_linked_list_rev_nth o8 i =
               ntp4vc_linked_list_rev_nth
                 o7 (i - (&(LENGTH l1pM):int)))
            ==>
            ~(p = null) /\
            ((&0:int) <= (&(LENGTH pM):int) /\
             LENGTH (TL pM) < LENGTH pM) /\
            ~(next1 p = null) /\
            ntp4vc_linked_list_rev_list_seg
              null next1 l1 o8 (next1 p) /\
            ntp4vc_linked_list_rev_list_seg
              null next1 (next1 p) (TL pM) null /\
            APPEND o8 (TL pM) = l1M /\
            ntp4vc_linked_list_rev_disjoint o8 (TL pM))
         else
           ~(p = null) /\
           ntp4vc_linked_list_rev_list_seg
             null (ntp4vc_linked_list_rev_function_update next1 p l2)
             l1 (APPEND l1M l2M) null)`;;

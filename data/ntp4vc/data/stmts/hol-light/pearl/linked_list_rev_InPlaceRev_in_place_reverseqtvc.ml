(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/linked_list_rev_InPlaceRev_in_place_reverseqtvc: the verification
  condition for in-place linked-list reversal, expressing the initial loop
  invariant and its preservation under a next-pointer update. This file
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
  !l:A.
  !next1:A->A.
  !lM:A list.
    (!x y:A. (eq_loc x y = T <=> x = y))
    ==>
    ntp4vc_linked_list_rev_list_seg null next1 l lM null
    ==>
    ntp4vc_linked_list_rev_list_seg null next1 l lM null /\
    ntp4vc_linked_list_rev_list_seg null next1 null [] null /\
    ntp4vc_linked_list_rev_disjoint lM [] /\
    APPEND (REVERSE lM) [] = REVERSE lM /\
    (!rM:A list.
     !r:A.
     !pM:A list.
     !p:A.
     !next2:A->A.
       ntp4vc_linked_list_rev_list_seg null next2 p pM null /\
       ntp4vc_linked_list_rev_list_seg null next2 r rM null /\
       ntp4vc_linked_list_rev_disjoint pM rM /\
       APPEND (REVERSE pM) rM = REVERSE lM
       ==>
       let o1 = null in
       let o2 = eq_loc p o1 in
       (o2 = T <=> p = o1)
       ==>
       if ~(o2 = T) then
         ~(p = null) /\
         (if pM = [] then
            F
          else
            let h = HD pM in
            let t = TL pM in
            (if pM = [] then F else TL pM = t) /\
            ntp4vc_linked_list_rev_list_seg
              null
              (ntp4vc_linked_list_rev_function_update next2 p r)
              (next2 p) t null /\
            ntp4vc_linked_list_rev_list_seg
              null
              (ntp4vc_linked_list_rev_function_update next2 p r)
              p (CONS h rM) null /\
            ntp4vc_linked_list_rev_disjoint t (CONS h rM) /\
            APPEND (REVERSE t) (CONS h rM) = REVERSE lM)
       else
         ntp4vc_linked_list_rev_list_seg
           null next2 r (REVERSE lM) null)`;;

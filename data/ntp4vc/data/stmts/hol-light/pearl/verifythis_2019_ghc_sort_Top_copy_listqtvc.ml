(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2019_ghc_sort_Top_copy_listqtvc: the verification
  condition for copying an integer list into an array suffix while preserving
  copied values, the untouched prefix, and occurrence counts. This file
  contains no proof.
*)

let ntp4vc_copy_list_index = new_definition
 `ntp4vc_copy_list_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ntp4vc_copy_list_nth = new_definition
 `ntp4vc_copy_list_nth (a:int list) (i:int) =
    if i < (&0:int) then
      (&0:int)
    else if ntp4vc_copy_list_index i < LENGTH a then
      EL (ntp4vc_copy_list_index i) a
    else
      (&0:int)`;;

let ntp4vc_copy_list_update =
  new_recursive_definition list_RECURSION
   `(!n:num.
     !x:int.
       ntp4vc_copy_list_update ([]:int list) n x = []) /\
    (!h:int.
     !t:int list.
     !n:num.
     !x:int.
       ntp4vc_copy_list_update (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (ntp4vc_copy_list_update t (PRE n) x))`;;

let ntp4vc_copy_list_count =
  new_recursive_definition list_RECURSION
   `(!x:int.
       ntp4vc_copy_list_count x ([]:int list) = (&0:int)) /\
    (!x:int.
     !h:int.
     !t:int list.
       ntp4vc_copy_list_count x (CONS h t) =
       (if h = x then (&1:int) else (&0:int)) +
       ntp4vc_copy_list_count x t)`;;

let ntp4vc_copy_list_map_occ = new_definition
 `ntp4vc_copy_list_map_occ
    (x:int) (a:int list) (l:int) (u:int) =
    (&(CARD
       {i:int |
          l <= i /\ i < u /\ ntp4vc_copy_list_nth a i = x}):int)`;;

let ntp4vc_copy_list_segment = new_definition
 `ntp4vc_copy_list_segment
    (destination:int list) (source:int list) (offset:int) <=>
    !x:int.
      offset <= x /\ x < (&(LENGTH destination):int)
      ==> ntp4vc_copy_list_nth destination x =
          ntp4vc_copy_list_nth source (x - offset)`;;

let ntp4vc_copy_list_prefix = new_definition
 `ntp4vc_copy_list_prefix
    (left:int list) (right:int list) (upper:int) <=>
    !x:int.
      (&0:int) <= x /\ x < upper
      ==> ntp4vc_copy_list_nth left x =
          ntp4vc_copy_list_nth right x`;;

let ntp4vc_copy_list_occurrences = new_definition
 `ntp4vc_copy_list_occurrences
    (array:int list) (source:int list) (offset:int) <=>
    !x:int.
      ntp4vc_copy_list_map_occ
        x array offset (&(LENGTH array):int) =
      ntp4vc_copy_list_count x source`;;

let statement =
 `!s:int.
  !l:int list.
  !a:int list.
    (&0:int) <= s
    ==>
    (&(LENGTH l):int) = (&(LENGTH a):int) - s
    ==>
    if l = [] then
      ntp4vc_copy_list_segment a l s /\
      ntp4vc_copy_list_occurrences a l s
    else
      let h = HD l in
      let t = TL l in
      let updated =
        ntp4vc_copy_list_update
          a (ntp4vc_copy_list_index s) h in
      ((&0:int) <= s /\ s < (&(LENGTH a):int)) /\
      (LENGTH updated = LENGTH a
       ==>
       (\r:int. ntp4vc_copy_list_nth updated r) =
         (\r:int.
            if r = s then h else ntp4vc_copy_list_nth a r)
       ==>
       let o1 = s + (&1:int) in
       ((TL l = t /\
         (&0:int) <= o1 /\
         (&(LENGTH t):int) = (&(LENGTH updated):int) - o1) /\
        (!a1:int list.
           LENGTH a1 = LENGTH updated
           ==>
           (ntp4vc_copy_list_segment a1 t o1 /\
            ntp4vc_copy_list_prefix a1 updated o1 /\
            ntp4vc_copy_list_occurrences a1 t o1)
           ==>
           (ntp4vc_copy_list_segment a1 l s /\
            ntp4vc_copy_list_prefix a1 a s /\
            ntp4vc_copy_list_occurrences a1 l s))))`;;

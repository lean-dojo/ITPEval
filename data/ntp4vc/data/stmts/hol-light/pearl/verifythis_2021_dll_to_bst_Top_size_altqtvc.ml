(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_dll_to_bst_Top_size_altqtvc: preservation of the
  doubly-linked-list loop invariant and decrease of the remaining-length
  variant during iterative list-size computation. This file contains no proof.
*)

let ntp4vc_dll_bst_int_index = new_definition
 `ntp4vc_dll_bst_int_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ntp4vc_dll_bst_nth = new_definition
 `ntp4vc_dll_bst_nth (xs:A list) (i:int) =
    if ntp4vc_dll_bst_int_index i < LENGTH xs
    then EL (ntp4vc_dll_bst_int_index i) xs
    else ARB`;;

let ntp4vc_dll_bst_fmap_domain = new_definition
 `ntp4vc_dll_bst_fmap_domain (m:A->B option) =
    {key:A | ?value:B. m key = SOME value}`;;

let ntp4vc_dll_bst_fmap_lookup = new_definition
 `ntp4vc_dll_bst_fmap_lookup (key:A) (m:A->B option) =
    @value:B. m key = SOME value`;;

let ntp4vc_dll_bst_option_the = new_definition
 `ntp4vc_dll_bst_option_the (value:A option) =
    @x:A. value = SOME x`;;

let ntp4vc_dll_bst_valid = new_definition
 `ntp4vc_dll_bst_valid
    (null:A)
    (prev:A->A option)
    (next:A->A option)
    (s:A list) <=>
    !i:int.
      (&0:int) <= i /\ i < (&(LENGTH s):int)
      ==>
      ~(ntp4vc_dll_bst_nth s i = null) /\
      ntp4vc_dll_bst_nth s i IN
        ntp4vc_dll_bst_fmap_domain prev /\
      ntp4vc_dll_bst_nth s i IN
        ntp4vc_dll_bst_fmap_domain next /\
      (!j:int.
         i < j /\ j < (&(LENGTH s):int)
         ==> ~(ntp4vc_dll_bst_nth s i =
               ntp4vc_dll_bst_nth s j))`;;

let ntp4vc_dll_bst_dll = new_definition
 `ntp4vc_dll_bst_dll
    (null:A)
    (prev:A->A option)
    (next:A->A option)
    (s:A list)
    (head:A)
    (lo:int)
    (hi:int) <=>
    ntp4vc_dll_bst_valid null prev next s /\
    (&0:int) <= lo /\ lo <= hi /\ hi <= (&(LENGTH s):int) /\
    head =
      (if lo = (&(LENGTH s):int)
       then null
       else ntp4vc_dll_bst_nth s lo) /\
    (!i:int.
       lo <= i /\ i < hi - (&1:int)
       ==>
       ntp4vc_dll_bst_fmap_lookup
         (ntp4vc_dll_bst_nth s i) next =
       ntp4vc_dll_bst_nth s (i + (&1:int))) /\
    (!i:int.
       lo < i /\ i < hi
       ==>
       ntp4vc_dll_bst_fmap_lookup
         (ntp4vc_dll_bst_nth s i) prev =
       ntp4vc_dll_bst_nth s (i - (&1:int))) /\
    (lo < hi
     ==>
     ntp4vc_dll_bst_fmap_lookup
       (ntp4vc_dll_bst_nth s (hi - (&1:int))) next =
     (if hi = (&(LENGTH s):int)
      then null
      else ntp4vc_dll_bst_nth s hi)) /\
    (lo < hi
     ==>
     ntp4vc_dll_bst_fmap_lookup
       (ntp4vc_dll_bst_nth s lo) prev =
     (if lo = (&0:int)
      then null
      else ntp4vc_dll_bst_nth s (lo - (&1:int))))`;;

let statement =
 `!to_fmap:A->B->B option.
  !null:B.
  !prev next:A.
  !s:B list.
  !head:B.
    (!container:A.
       FINITE (ntp4vc_dll_bst_fmap_domain (to_fmap container)))
    ==>
    ntp4vc_dll_bst_dll
      null (to_fmap prev) (to_fmap next) s head
      (&0:int) (&(LENGTH s):int)
    ==>
    ntp4vc_dll_bst_dll
      null (to_fmap prev) (to_fmap next) s head
      (&0:int) (&(LENGTH s):int) /\
    (!len:int.
     !p:B.
       ntp4vc_dll_bst_dll
         null (to_fmap prev) (to_fmap next) s p
         len (&(LENGTH s):int)
       ==>
       (if ~(p = null) then
          p IN
            ntp4vc_dll_bst_fmap_domain (to_fmap next) /\
          (let o1 =
             ntp4vc_dll_bst_fmap_lookup p (to_fmap next) in
           o1 = ntp4vc_dll_bst_option_the ((to_fmap next) p)
           ==>
           ((&0:int) <= (&(LENGTH s):int) - len /\
            (&(LENGTH s):int) - (len + (&1:int)) <
              (&(LENGTH s):int) - len) /\
           ntp4vc_dll_bst_dll
             null (to_fmap prev) (to_fmap next) s o1
             (len + (&1:int)) (&(LENGTH s):int))
        else
          len = (&(LENGTH s):int)))`;;

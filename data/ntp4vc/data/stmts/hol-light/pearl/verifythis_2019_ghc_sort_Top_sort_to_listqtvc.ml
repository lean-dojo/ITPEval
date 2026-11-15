(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2019_ghc_sort_Top_sort_to_listqtvc: the verification
  condition connecting monotonic cutpoints, sorted segment lists, and the
  sorted occurrence- and length-preserving result of GHC sort_to_list.
  This file contains no proof.
*)

let ntp4vc_stl_index = new_definition
 `ntp4vc_stl_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ntp4vc_stl_nth = new_definition
 `ntp4vc_stl_nth (xs:int list) (i:int) =
    if ntp4vc_stl_index i < LENGTH xs
    then EL (ntp4vc_stl_index i) xs
    else (&0:int)`;;

let ntp4vc_stl_count =
  new_recursive_definition list_RECURSION
   `(!x:int.
       ntp4vc_stl_count x ([]:int list) = (&0:int)) /\
    (!x:int.
     !h:int.
     !t:int list.
       ntp4vc_stl_count x (CONS h t) =
       (if h = x then (&1:int) else (&0:int)) +
       ntp4vc_stl_count x t)`;;

let ntp4vc_stl_flatten =
  new_recursive_definition list_RECURSION
   `(ntp4vc_stl_flatten ([]:(int list)list) = ([]:int list)) /\
    (!h:int list.
     !t:(int list)list.
       ntp4vc_stl_flatten (CONS h t) =
       APPEND h (ntp4vc_stl_flatten t))`;;

let ntp4vc_stl_sorted =
  new_recursive_definition list_RECURSION
   `(ntp4vc_stl_sorted ([]:int list) = T) /\
    (!h:int.
     !t:int list.
       ntp4vc_stl_sorted (CONS h t) =
       if t = [] then T
       else h <= HD t /\ ntp4vc_stl_sorted t)`;;

let ntp4vc_stl_permut = new_definition
 `ntp4vc_stl_permut (left:int list) (right:int list) <=>
    LENGTH left = LENGTH right /\
    (!x:int.
       ntp4vc_stl_count x left = ntp4vc_stl_count x right)`;;

let ntp4vc_stl_map_occ = new_definition
 `ntp4vc_stl_map_occ
    (x:int) (a:int list) (lower:int) (upper:int) =
    (&(CARD
       {i:int |
          lower <= i /\ i < upper /\ ntp4vc_stl_nth a i = x}):int)`;;

let ntp4vc_stl_seq = new_definition
 `ntp4vc_stl_seq (cutpoints:int list) = REVERSE cutpoints`;;

let ntp4vc_stl_seq_nth = new_definition
 `ntp4vc_stl_seq_nth (cutpoints:int list) (i:int) =
    ntp4vc_stl_nth (ntp4vc_stl_seq cutpoints) i`;;

let ntp4vc_stl_first = new_definition
 `ntp4vc_stl_first (cutpoints:int list) =
    ntp4vc_stl_seq_nth cutpoints (&0:int)`;;

let ntp4vc_stl_last = new_definition
 `ntp4vc_stl_last (cutpoints:int list) =
    ntp4vc_stl_seq_nth
      cutpoints
      ((&(LENGTH (ntp4vc_stl_seq cutpoints)):int) - (&1:int))`;;

let ntp4vc_stl_segment = new_definition
 `ntp4vc_stl_segment
    (a:int list) (lower:int) (upper:int) <=>
    (!z1 z2:int.
       lower <= z1 /\ z1 < z2 /\ z2 < upper
       ==> ntp4vc_stl_nth a z1 < ntp4vc_stl_nth a z2) \/
    (!z1 z2:int.
       lower <= z1 /\ z1 < z2 /\ z2 < upper
       ==> ntp4vc_stl_nth a z2 <= ntp4vc_stl_nth a z1)`;;

let ntp4vc_stl_all_segments = new_definition
 `ntp4vc_stl_all_segments
    (a:int list) (cutpoints:int list) <=>
    !k:int.
      (&0:int) <= k /\
      k < (&(LENGTH (ntp4vc_stl_seq cutpoints)):int) - (&1:int)
      ==>
      ntp4vc_stl_segment
        a
        (ntp4vc_stl_seq_nth cutpoints k)
        (ntp4vc_stl_seq_nth cutpoints (k + (&1:int)))`;;

let ntp4vc_stl_seq_sorted = new_definition
 `ntp4vc_stl_seq_sorted (cutpoints:int list) <=>
    !i j:int.
      (&0:int) <= i /\
      i < j /\
      j < (&(LENGTH (ntp4vc_stl_seq cutpoints)):int)
      ==>
      ntp4vc_stl_seq_nth cutpoints i <=
      ntp4vc_stl_seq_nth cutpoints j`;;

let ntp4vc_stl_cutpoint_bounds = new_definition
 `ntp4vc_stl_cutpoint_bounds
    (cutpoints:int list) (upper:int) <=>
    !z:int.
      MEM z cutpoints
      ==> (&0:int) <= z /\ z <= upper`;;

let ntp4vc_stl_cutpoint_contract = new_definition
 `ntp4vc_stl_cutpoint_contract
    (a:int list) (cutpoints:int list) <=>
    ntp4vc_stl_first cutpoints = (&0:int) /\
    ntp4vc_stl_last cutpoints = (&(LENGTH a):int) /\
    (&2:int) <= (&(LENGTH cutpoints):int) /\
    ntp4vc_stl_cutpoint_bounds
      cutpoints (&(LENGTH a):int) /\
    ntp4vc_stl_all_segments a cutpoints /\
    ntp4vc_stl_seq_sorted cutpoints`;;

let ntp4vc_stl_sorted_lists_contract = new_definition
 `ntp4vc_stl_sorted_lists_contract
    (a:int list) (cutpoints:int list) (lists:(int list)list) <=>
    (!l:int list.
       MEM l lists ==> ntp4vc_stl_sorted l) /\
    (!x:int.
       ntp4vc_stl_count x (ntp4vc_stl_flatten lists) =
       ntp4vc_stl_map_occ
         x a
         (ntp4vc_stl_first cutpoints)
         (ntp4vc_stl_last cutpoints))`;;

let ntp4vc_stl_result_contract = new_definition
 `ntp4vc_stl_result_contract
    (a:int list) (lists:(int list)list) (result:int list) <=>
    ntp4vc_stl_sorted result /\
    (!x:int.
       ntp4vc_stl_map_occ
         x a (&0:int) (&(LENGTH a):int) =
       ntp4vc_stl_count x result) /\
    LENGTH result = LENGTH a`;;

let ntp4vc_stl_after_cutpoints = new_definition
 `ntp4vc_stl_after_cutpoints
    (a:int list) (cutpoints:int list) <=>
    (&0:int) < (&(LENGTH cutpoints):int) /\
    ntp4vc_stl_seq_sorted cutpoints /\
    ntp4vc_stl_cutpoint_bounds
      cutpoints (&(LENGTH a):int) /\
    ntp4vc_stl_all_segments a cutpoints /\
    (!lists:(int list)list.
       ntp4vc_stl_sorted_lists_contract a cutpoints lists
       ==>
       (!l:int list.
          MEM l lists ==> ntp4vc_stl_sorted l) /\
       (!result:int list.
          ntp4vc_stl_sorted result /\
          ntp4vc_stl_permut
            result (ntp4vc_stl_flatten lists)
          ==>
          ntp4vc_stl_result_contract a lists result))`;;

let statement =
 `!a:int list.
    (&0:int) < (&(LENGTH a):int)
    ==>
    (&0:int) < (&(LENGTH a):int) /\
    (!cutpoints:int list.
       ntp4vc_stl_cutpoint_contract a cutpoints
       ==>
       ntp4vc_stl_after_cutpoints a cutpoints)`;;

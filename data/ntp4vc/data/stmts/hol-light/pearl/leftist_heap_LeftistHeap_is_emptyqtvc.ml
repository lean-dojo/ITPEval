(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/leftist_heap_LeftistHeap_is_emptyqtvc: a leftist-tree emptiness
  verification condition relating the Boolean result of the constructor test
  to the recursively defined integer size. This file contains no proof.
*)

let ntp4vc_leftist_empty_tree_INDUCT,
    ntp4vc_leftist_empty_tree_RECURSION =
  define_type
    "ntp4vc_leftist_empty_tree =
       NTP4VCLeftistEmpty
     | NTP4VCLeftistNode
         int ntp4vc_leftist_empty_tree A ntp4vc_leftist_empty_tree";;

let ntp4vc_leftist_empty_size =
  new_recursive_definition ntp4vc_leftist_empty_tree_RECURSION
   `(ntp4vc_leftist_empty_size
       (NTP4VCLeftistEmpty:A ntp4vc_leftist_empty_tree) =
       (&0:int)) /\
    (!s:int.
     !l r:A ntp4vc_leftist_empty_tree.
     !x:A.
       ntp4vc_leftist_empty_size (NTP4VCLeftistNode s l x r) =
       (&1:int) +
       ntp4vc_leftist_empty_size l +
       ntp4vc_leftist_empty_size r)`;;

let ntp4vc_leftist_empty_result =
  new_recursive_definition ntp4vc_leftist_empty_tree_RECURSION
   `(!result:bool.
       ntp4vc_leftist_empty_result
         result (NTP4VCLeftistEmpty:A ntp4vc_leftist_empty_tree) =
       (result = T)) /\
    (!result:bool.
     !s:int.
     !l r:A ntp4vc_leftist_empty_tree.
     !x:A.
       ntp4vc_leftist_empty_result
         result (NTP4VCLeftistNode s l x r) =
       (result = F))`;;

let statement =
 `!h:A ntp4vc_leftist_empty_tree.
  !result:bool.
    ntp4vc_leftist_empty_result result h
    ==>
    (result = T <=>
     ntp4vc_leftist_empty_size h = (&0:int))`;;

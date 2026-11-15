(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/tree_of_list_TreeOfList_tree_of_listqtvc: the verification condition
  connecting the auxiliary list-to-tree result with inorder preservation and
  logarithmic tree-height bounds. This file contains no proof.
*)

let ntp4vc_tree_of_list_tree_INDUCT,
    ntp4vc_tree_of_list_tree_RECURSION =
  define_type
    "ntp4vc_tree_of_list_tree =
       NTP4VCTreeOfListEmpty
     | NTP4VCTreeOfListNode
         ntp4vc_tree_of_list_tree A ntp4vc_tree_of_list_tree";;

let ntp4vc_tree_of_list_int_max = new_definition
 `ntp4vc_tree_of_list_int_max (x:int) (y:int) =
    if x <= y then y else x`;;

let ntp4vc_tree_of_list_size =
  new_recursive_definition ntp4vc_tree_of_list_tree_RECURSION
   `(ntp4vc_tree_of_list_size
       (NTP4VCTreeOfListEmpty:A ntp4vc_tree_of_list_tree) =
       (&0:int)) /\
    (!l r:A ntp4vc_tree_of_list_tree.
     !x:A.
       ntp4vc_tree_of_list_size
         (NTP4VCTreeOfListNode l x r) =
       (&1:int) +
       ntp4vc_tree_of_list_size l +
       ntp4vc_tree_of_list_size r)`;;

let ntp4vc_tree_of_list_height =
  new_recursive_definition ntp4vc_tree_of_list_tree_RECURSION
   `(ntp4vc_tree_of_list_height
       (NTP4VCTreeOfListEmpty:A ntp4vc_tree_of_list_tree) =
       (&0:int)) /\
    (!l r:A ntp4vc_tree_of_list_tree.
     !x:A.
       ntp4vc_tree_of_list_height
         (NTP4VCTreeOfListNode l x r) =
       (&1:int) +
       ntp4vc_tree_of_list_int_max
         (ntp4vc_tree_of_list_height l)
         (ntp4vc_tree_of_list_height r))`;;

let ntp4vc_tree_of_list_inorder =
  new_recursive_definition ntp4vc_tree_of_list_tree_RECURSION
   `(ntp4vc_tree_of_list_inorder
       (NTP4VCTreeOfListEmpty:A ntp4vc_tree_of_list_tree) =
       ([]:A list)) /\
    (!l r:A ntp4vc_tree_of_list_tree.
     !x:A.
       ntp4vc_tree_of_list_inorder
         (NTP4VCTreeOfListNode l x r) =
       APPEND
         (ntp4vc_tree_of_list_inorder l)
         (CONS x (ntp4vc_tree_of_list_inorder r)))`;;

let ntp4vc_tree_of_list_power = new_definition
 `ntp4vc_tree_of_list_power (base:int) (exponent:int) =
    base pow
      (if exponent < (&0:int) then 0 else num_of_int exponent)`;;

let statement =
 `!l:A list.
    let o1 = (&(LENGTH l):int) in
    ((&0:int) <= o1 /\ o1 <= (&(LENGTH l):int)) /\
    (!o2:A ntp4vc_tree_of_list_tree.
     !o3:A list.
       (APPEND (ntp4vc_tree_of_list_inorder o2) o3 = l /\
        ntp4vc_tree_of_list_size o2 = o1 /\
        ((&0:int) < o1
         ==>
         let h = ntp4vc_tree_of_list_height o2 in
         ntp4vc_tree_of_list_power (&2:int) (h - (&1:int)) <= o1 /\
         o1 < ntp4vc_tree_of_list_power (&2:int) h))
       ==>
       ntp4vc_tree_of_list_inorder o2 = l /\
       ((&0:int) < ntp4vc_tree_of_list_size o2
        ==>
        let h = ntp4vc_tree_of_list_height o2 in
        ntp4vc_tree_of_list_power (&2:int) (h - (&1:int)) <=
          ntp4vc_tree_of_list_size o2 /\
        ntp4vc_tree_of_list_size o2 <
          ntp4vc_tree_of_list_power (&2:int) h))`;;

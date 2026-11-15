(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/tree_of_list_TreeOfList_tree_of_listqtvc: the verification condition
  for converting a list to a binary tree while preserving inorder traversal
  and logarithmic height bounds. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  tree_of_list_tree =
    TreeOfListEmpty
  | TreeOfListNode tree_of_list_tree 'elt tree_of_list_tree
End

val tree_of_list_max_def = Define `
  tree_of_list_max (x : int) y =
    if x < y then y else x`;

val tree_of_list_size_def = Define `
  (tree_of_list_size
      (TreeOfListEmpty : 'elt tree_of_list_tree) = (0 : int)) /\
  (tree_of_list_size (TreeOfListNode l x r) =
     (1 : int) + tree_of_list_size l + tree_of_list_size r)`;

val tree_of_list_height_def = Define `
  (tree_of_list_height
      (TreeOfListEmpty : 'elt tree_of_list_tree) = (0 : int)) /\
  (tree_of_list_height (TreeOfListNode l x r) =
     (1 : int) +
       tree_of_list_max
         (tree_of_list_height l)
         (tree_of_list_height r))`;

val tree_of_list_inorder_def = Define `
  (tree_of_list_inorder
      (TreeOfListEmpty : 'elt tree_of_list_tree) = []) /\
  (tree_of_list_inorder (TreeOfListNode l x r) =
     tree_of_list_inorder l ++ x::tree_of_list_inorder r)`;

val tree_of_list_to_num_def = Define `
  tree_of_list_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val tree_of_list_power_def = Define `
  tree_of_list_power (base : int) (exponent : int) =
    base ** tree_of_list_to_num exponent`;

val tree_of_list_TreeOfList_tree_of_listqtvc_statement =
  ``!l : 'elt list.
      let o1 = &(LENGTH l)
      in
        ((0 : int) <= o1 /\ o1 <= &(LENGTH l)) /\
        (!o2 : 'elt tree_of_list_tree.
         !o3 : 'elt list.
           tree_of_list_inorder o2 ++ o3 = l /\
           tree_of_list_size o2 = o1 /\
           ((0 : int) < o1 ==>
            let h = tree_of_list_height o2
            in
              tree_of_list_power (2 : int) (h - (1 : int)) <= o1 /\
              o1 < tree_of_list_power (2 : int) h)
           ==>
           tree_of_list_inorder o2 = l /\
           ((0 : int) < tree_of_list_size o2 ==>
            let h = tree_of_list_height o2
            in
              tree_of_list_power (2 : int) (h - (1 : int)) <=
                tree_of_list_size o2 /\
              tree_of_list_size o2 <
                tree_of_list_power (2 : int) h))``;

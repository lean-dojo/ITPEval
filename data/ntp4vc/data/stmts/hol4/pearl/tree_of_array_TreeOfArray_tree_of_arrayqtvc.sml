(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/tree_of_array_TreeOfArray_tree_of_arrayqtvc: the verification
  condition for converting an array to a binary tree while preserving inorder
  traversal and logarithmic height bounds. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  tree_of_array_tree =
    TreeOfArrayEmpty
  | TreeOfArrayNode tree_of_array_tree 'a tree_of_array_tree
End

val tree_of_array_max_def = Define `
  tree_of_array_max (x : int) y =
    if x < y then y else x`;

val tree_of_array_size_def = Define `
  (tree_of_array_size
      (TreeOfArrayEmpty : 'a tree_of_array_tree) = (0 : int)) /\
  (tree_of_array_size (TreeOfArrayNode l x r) =
     (1 : int) + tree_of_array_size l + tree_of_array_size r)`;

val tree_of_array_height_def = Define `
  (tree_of_array_height
      (TreeOfArrayEmpty : 'a tree_of_array_tree) = (0 : int)) /\
  (tree_of_array_height (TreeOfArrayNode l x r) =
     (1 : int) +
       tree_of_array_max
         (tree_of_array_height l)
         (tree_of_array_height r))`;

val tree_of_array_inorder_def = Define `
  (tree_of_array_inorder
      (TreeOfArrayEmpty : 'a tree_of_array_tree) = []) /\
  (tree_of_array_inorder (TreeOfArrayNode l x r) =
     tree_of_array_inorder l ++ x::tree_of_array_inorder r)`;

val tree_of_array_to_num_def = Define `
  tree_of_array_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val tree_of_array_TreeOfArray_tree_of_arrayqtvc_statement =
  ``!a : 'a list.
      let o1 = &(LENGTH a)
      in
        ((0 : int) <= (0 : int) /\
         (0 : int) <= o1 /\
         o1 <= &(LENGTH a)) /\
        (!result : 'a tree_of_array_tree.
           (let n = o1 - (0 : int)
            in
              tree_of_array_size result = n /\
              tree_of_array_inorder result =
                DROP (0 : num)
                  (TAKE
                    (tree_of_array_to_num o1 - (0 : num))
                    a) /\
              ((0 : int) < n ==>
               let h = tree_of_array_height result
               in
                 (2 : int) **
                     tree_of_array_to_num (h - (1 : int)) <= n /\
                 n <
                   (2 : int) ** tree_of_array_to_num h))
           ==>
           tree_of_array_inorder result =
             DROP (0 : num)
               (TAKE (LENGTH a - (0 : num)) a) /\
           ((0 : int) < tree_of_array_size result ==>
            let h = tree_of_array_height result
            in
              (2 : int) **
                  tree_of_array_to_num (h - (1 : int)) <=
                tree_of_array_size result /\
              tree_of_array_size result <
                (2 : int) ** tree_of_array_to_num h))``;

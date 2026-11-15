(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vstte12_tree_reconstruction_Harness_harnessqtvc: existence and
  uniqueness of the binary tree whose left-to-right leaf-depth sequence from
  root depth zero is [1, 3, 3, 2]. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  vstte12_tree_reconstruction_tree =
    Vstte12TreeLeaf
  | Vstte12TreeNode
      vstte12_tree_reconstruction_tree
      vstte12_tree_reconstruction_tree
End

val vstte12_tree_reconstruction_depths_def = Define `
  (vstte12_tree_reconstruction_depths
      (d : int) Vstte12TreeLeaf = [d]) /\
  (vstte12_tree_reconstruction_depths
      d (Vstte12TreeNode left right) =
     vstte12_tree_reconstruction_depths (d + (1 : int)) left ++
     vstte12_tree_reconstruction_depths (d + (1 : int)) right)`;

val vstte12_tree_reconstruction_Harness_harnessqtvc_statement =
  ``(!result : vstte12_tree_reconstruction_tree.
       vstte12_tree_reconstruction_depths (0 : int) result =
         [(1 : int); (3 : int); (3 : int); (2 : int)] ==>
       result =
         Vstte12TreeNode
           Vstte12TreeLeaf
           (Vstte12TreeNode
              (Vstte12TreeNode Vstte12TreeLeaf Vstte12TreeLeaf)
              Vstte12TreeLeaf)) /\
    ~(!t : vstte12_tree_reconstruction_tree.
        ~(vstte12_tree_reconstruction_depths (0 : int) t =
          [(1 : int); (3 : int); (3 : int); (2 : int)]))``;

(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vstte12_tree_reconstruction_Harness_harness2qtvc: no finite binary
  tree has the left-to-right leaf-depth list [1, 3, 2, 2] when its root is
  at depth zero. This file contains no proof.
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

val vstte12_tree_reconstruction_Harness_harness2qtvc_statement =
  ``!x : vstte12_tree_reconstruction_tree.
      ~(vstte12_tree_reconstruction_depths (0 : int) x =
        [(1 : int); (3 : int); (2 : int); (2 : int)])``;

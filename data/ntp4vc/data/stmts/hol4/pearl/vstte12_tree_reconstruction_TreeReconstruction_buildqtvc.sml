(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vstte12_tree_reconstruction_TreeReconstruction_buildqtvc: the
  binary-tree reconstruction verification condition relating leaf-depth list
  decompositions to exact reconstruction and failure. This file contains no
  proof.
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

val vstte12_tree_reconstruction_TreeReconstruction_buildqtvc_statement =
  ``!s1 : int list.
      (!t : vstte12_tree_reconstruction_tree. !s : int list.
         s1 = vstte12_tree_reconstruction_depths (0 : int) t ++ s ==>
         (case s of
            [] =>
              vstte12_tree_reconstruction_depths (0 : int) t = s1
          | h::tail =>
              !t1 : vstte12_tree_reconstruction_tree.
                ~(vstte12_tree_reconstruction_depths
                    (0 : int) t1 = s1))) /\
      ((!t : vstte12_tree_reconstruction_tree. !s' : int list.
          ~(vstte12_tree_reconstruction_depths (0 : int) t ++ s' = s1)) ==>
       (!t : vstte12_tree_reconstruction_tree.
          ~(vstte12_tree_reconstruction_depths (0 : int) t = s1)))``;

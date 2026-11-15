(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vstte12_tree_reconstruction_TreeReconstruction_build_recqtvc: the
  recursive binary-tree reconstruction verification condition, including
  depth-list decomposition, failure cases, and lexicographic termination
  obligations. This file contains no proof.
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

val vstte12_tree_reconstruction_TreeReconstruction_build_recqtvc_statement =
  ``!s : int list. !d : int.
      case s of
        [] =>
          !t : vstte12_tree_reconstruction_tree. !s' : int list.
            ~(vstte12_tree_reconstruction_depths d t ++ s' = s)
      | h::tail =>
          if h < d then
            !t1 : vstte12_tree_reconstruction_tree. !s' : int list.
              ~(vstte12_tree_reconstruction_depths d t1 ++ s' = s)
          else if h = d then
            s =
              vstte12_tree_reconstruction_depths
                d Vstte12TreeLeaf ++ tail
          else
            let o1 = d + (1 : int) in
              ((0 : int) <= HD s - d /\
               HD s - o1 < HD s - d) /\
              (!l : vstte12_tree_reconstruction_tree. !s1 : int list.
                 s =
                   vstte12_tree_reconstruction_depths o1 l ++ s1 ==>
                 let o2 = d + (1 : int) in
                   (((0 : int) <= &(LENGTH s) /\
                     &(LENGTH s1) < &(LENGTH s)) \/
                    (LENGTH s = LENGTH s1 /\
                     (0 : int) <= HD s - d /\
                     HD s1 - o2 < HD s - d)) /\
                   (!r : vstte12_tree_reconstruction_tree. !s2 : int list.
                      s1 =
                        vstte12_tree_reconstruction_depths o2 r ++ s2 ==>
                      s =
                        vstte12_tree_reconstruction_depths d
                          (Vstte12TreeNode l r) ++ s2) /\
                   ((!t1 : vstte12_tree_reconstruction_tree.
                       !s' : int list.
                         ~(vstte12_tree_reconstruction_depths
                             o2 t1 ++ s' = s1)) ==>
                    (!t1 : vstte12_tree_reconstruction_tree.
                       !s' : int list.
                         ~(vstte12_tree_reconstruction_depths
                             d t1 ++ s' = s)))) /\
              ((!t1 : vstte12_tree_reconstruction_tree. !s' : int list.
                  ~(vstte12_tree_reconstruction_depths o1 t1 ++ s' = s)) ==>
               (!t1 : vstte12_tree_reconstruction_tree. !s' : int list.
                  ~(vstte12_tree_reconstruction_depths d t1 ++ s' = s)))``;

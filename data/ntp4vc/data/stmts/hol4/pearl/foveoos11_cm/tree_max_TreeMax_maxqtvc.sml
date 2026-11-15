(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/foveoos11_cm/tree_max_TreeMax_maxqtvc: an integer binary-tree
  maximum verification condition stating that the result assembled from
  right- and left-subtree maxima is an upper bound and a member of the
  original nonempty tree. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  tree_max_tree =
    TreeMaxNull
  | TreeMaxTree int tree_max_tree tree_max_tree
End

val tree_max_mem_def = Define `
  (tree_max_mem (v : int) TreeMaxNull = F) /\
  (tree_max_mem v (TreeMaxTree x l r) =
     (x = v \/ tree_max_mem v l \/ tree_max_mem v r))`;

val tree_max_ge_tree_def = Define `
  (tree_max_ge_tree (v : int) TreeMaxNull = T) /\
  (tree_max_ge_tree v (TreeMaxTree x l r) =
     (x <= v /\ tree_max_ge_tree v l /\ tree_max_ge_tree v r))`;

val tree_max_TreeMax_max_vc =
  ``!(t : tree_max_tree).
      ~(t = TreeMaxNull) ==>
      ((case t of
          TreeMaxNull => F
        | TreeMaxTree v l r => T) /\
       !result : int.
         (case t of
            TreeMaxNull => F
          | TreeMaxTree v l r =>
              ?o1 : int.
                (tree_max_ge_tree o1 r /\
                 v <= o1 /\
                 (o1 = v \/ tree_max_mem o1 r)) /\
                tree_max_ge_tree result l /\
                o1 <= result /\
                (result = o1 \/ tree_max_mem result l))
         ==>
         tree_max_ge_tree result t /\
         tree_max_mem result t)``;

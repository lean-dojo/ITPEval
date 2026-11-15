(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/foveoos11_cm/tree_max_TreeMax_max_auxqtvc: an integer binary-tree
  maximum-accumulator verification condition relating the two recursive
  subtree calls to the final upper-bound and membership result. This file
  contains no proof.
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

val tree_max_max_def = Define `
  tree_max_max (x : int) y = if x < y then y else x`;

val tree_max_TreeMax_max_aux_vc =
  ``!(t : tree_max_tree) (acc : int).
      (case t of
         TreeMaxNull => T
       | TreeMaxTree v l r =>
           let o1 = tree_max_max v acc
           in
             (case t of
                TreeMaxNull => F
              | TreeMaxTree _ f f1 => f = r \/ f1 = r) /\
             !o2 : int.
               tree_max_ge_tree o2 r /\
               o1 <= o2 /\
               (o2 = o1 \/ tree_max_mem o2 r)
               ==>
               (case t of
                  TreeMaxNull => F
                | TreeMaxTree _ f f1 => f = l \/ f1 = l)) /\
      !result : int.
        (case t of
           TreeMaxNull => result = acc
         | TreeMaxTree v l r =>
             let o1 = tree_max_max v acc
             in
               ?o2 : int.
                 (tree_max_ge_tree o2 r /\
                  o1 <= o2 /\
                  (o2 = o1 \/ tree_max_mem o2 r)) /\
                 tree_max_ge_tree result l /\
                 o2 <= result /\
                 (result = o2 \/ tree_max_mem result l))
        ==>
        tree_max_ge_tree result t /\
        acc <= result /\
        (result = acc \/ tree_max_mem result t)``;

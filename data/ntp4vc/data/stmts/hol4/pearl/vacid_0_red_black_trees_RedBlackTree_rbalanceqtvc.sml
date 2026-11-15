(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vacid_0_red_black_trees_RedBlackTree_rbalanceqtvc: the right-balancing
  verification condition for an integer-keyed red-black tree, preserving the
  binary-search invariant, black height, and key-value membership. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  rbalance_color =
    RBalanceRed
  | RBalanceBlack
End

Datatype:
  rbalance_tree =
    RBalanceLeaf
  | RBalanceNode rbalance_color rbalance_tree int int rbalance_tree
End

val rbalance_memt_def = Define `
  (rbalance_memt RBalanceLeaf k v = F) /\
  (rbalance_memt (RBalanceNode color left key value right) k v =
     ((k = key /\ v = value) \/
      rbalance_memt left k v \/
      rbalance_memt right k v))`;

val rbalance_lt_tree_def = Define `
  rbalance_lt_tree x t <=>
    !k : int. !v : int.
      rbalance_memt t k v ==> k < x`;

val rbalance_gt_tree_def = Define `
  rbalance_gt_tree x t <=>
    !k : int. !v : int.
      rbalance_memt t k v ==> x < k`;

val rbalance_bst_def = Define `
  (rbalance_bst RBalanceLeaf = T) /\
  (rbalance_bst (RBalanceNode color left key value right) =
     (rbalance_bst left /\
      rbalance_bst right /\
      rbalance_lt_tree key left /\
      rbalance_gt_tree key right))`;

val rbalance_is_not_red_def = Define `
  (rbalance_is_not_red RBalanceLeaf = T) /\
  (rbalance_is_not_red
      (RBalanceNode RBalanceRed left key value right) = F) /\
  (rbalance_is_not_red
      (RBalanceNode RBalanceBlack left key value right) = T)`;

val rbalance_rbtree_def = Define `
  (rbalance_rbtree n RBalanceLeaf = (n = (0 : int))) /\
  (rbalance_rbtree n
      (RBalanceNode RBalanceRed left key value right) =
     (rbalance_rbtree n left /\
      rbalance_rbtree n right /\
      rbalance_is_not_red left /\
      rbalance_is_not_red right)) /\
  (rbalance_rbtree n
      (RBalanceNode RBalanceBlack left key value right) =
     (rbalance_rbtree (n - (1 : int)) left /\
      rbalance_rbtree (n - (1 : int)) right))`;

val rbalance_almost_rbtree_def = Define `
  (rbalance_almost_rbtree n RBalanceLeaf = (n = (0 : int))) /\
  (rbalance_almost_rbtree n
      (RBalanceNode RBalanceRed left key value right) =
     (rbalance_rbtree n left /\ rbalance_rbtree n right)) /\
  (rbalance_almost_rbtree n
      (RBalanceNode RBalanceBlack left key value right) =
     (rbalance_rbtree (n - (1 : int)) left /\
      rbalance_rbtree (n - (1 : int)) right))`;

val vacid_0_red_black_trees_RedBlackTree_rbalanceqtvc_statement =
  ``!(k : int) (l : rbalance_tree) (r : rbalance_tree) (v : int).
      rbalance_lt_tree k l ==>
      rbalance_gt_tree k r ==>
      rbalance_bst l ==>
      rbalance_bst r ==>
      ((case r of
          RBalanceNode RBalanceRed
            (RBalanceNode RBalanceRed b ky vy c) kz vz d => T
        | RBalanceNode RBalanceRed b ky vy
            (RBalanceNode RBalanceRed c kz vz d) => T
        | _ => T) /\
       !result : rbalance_tree.
         (case r of
            RBalanceNode RBalanceRed
              (RBalanceNode RBalanceRed b ky vy c) kz vz d =>
                result =
                  RBalanceNode RBalanceRed
                    (RBalanceNode RBalanceBlack l k v b) ky vy
                    (RBalanceNode RBalanceBlack c kz vz d)
          | RBalanceNode RBalanceRed b ky vy
              (RBalanceNode RBalanceRed c kz vz d) =>
                result =
                  RBalanceNode RBalanceRed
                    (RBalanceNode RBalanceBlack l k v b) ky vy
                    (RBalanceNode RBalanceBlack c kz vz d)
          | _ =>
                result = RBalanceNode RBalanceBlack l k v r)
         ==>
         rbalance_bst result /\
         (!n : int.
            rbalance_almost_rbtree n r ==>
            rbalance_rbtree n l ==>
            rbalance_rbtree (n + (1 : int)) result) /\
         (!k' : int. !v' : int.
            rbalance_memt result k' v' <=>
              (if k' = k
               then v' = v
               else
                 rbalance_memt l k' v' \/
                 rbalance_memt r k' v')))``;

(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vacid_0_red_black_trees_RedBlackTree_lbalanceqtvc: the left-balancing
  verification condition for an integer-keyed red-black tree, preserving the
  binary-search invariant, black height, and key-value membership. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  lbalance_color =
    LBalanceRed
  | LBalanceBlack
End

Datatype:
  lbalance_tree =
    LBalanceLeaf
  | LBalanceNode lbalance_color lbalance_tree int int lbalance_tree
End

val lbalance_memt_def = Define `
  (lbalance_memt LBalanceLeaf k v = F) /\
  (lbalance_memt (LBalanceNode color left key value right) k v =
     ((k = key /\ v = value) \/
      lbalance_memt left k v \/
      lbalance_memt right k v))`;

val lbalance_lt_tree_def = Define `
  lbalance_lt_tree x t <=>
    !k : int. !v : int.
      lbalance_memt t k v ==> k < x`;

val lbalance_gt_tree_def = Define `
  lbalance_gt_tree x t <=>
    !k : int. !v : int.
      lbalance_memt t k v ==> x < k`;

val lbalance_bst_def = Define `
  (lbalance_bst LBalanceLeaf = T) /\
  (lbalance_bst (LBalanceNode color left key value right) =
     (lbalance_bst left /\
      lbalance_bst right /\
      lbalance_lt_tree key left /\
      lbalance_gt_tree key right))`;

val lbalance_is_not_red_def = Define `
  (lbalance_is_not_red LBalanceLeaf = T) /\
  (lbalance_is_not_red
      (LBalanceNode LBalanceRed left key value right) = F) /\
  (lbalance_is_not_red
      (LBalanceNode LBalanceBlack left key value right) = T)`;

val lbalance_rbtree_def = Define `
  (lbalance_rbtree n LBalanceLeaf = (n = (0 : int))) /\
  (lbalance_rbtree n
      (LBalanceNode LBalanceRed left key value right) =
     (lbalance_rbtree n left /\
      lbalance_rbtree n right /\
      lbalance_is_not_red left /\
      lbalance_is_not_red right)) /\
  (lbalance_rbtree n
      (LBalanceNode LBalanceBlack left key value right) =
     (lbalance_rbtree (n - (1 : int)) left /\
      lbalance_rbtree (n - (1 : int)) right))`;

val lbalance_almost_rbtree_def = Define `
  (lbalance_almost_rbtree n LBalanceLeaf = (n = (0 : int))) /\
  (lbalance_almost_rbtree n
      (LBalanceNode LBalanceRed left key value right) =
     (lbalance_rbtree n left /\ lbalance_rbtree n right)) /\
  (lbalance_almost_rbtree n
      (LBalanceNode LBalanceBlack left key value right) =
     (lbalance_rbtree (n - (1 : int)) left /\
      lbalance_rbtree (n - (1 : int)) right))`;

val vacid_0_red_black_trees_RedBlackTree_lbalanceqtvc_statement =
  ``!(k : int) (l : lbalance_tree) (r : lbalance_tree) (v : int).
      lbalance_lt_tree k l ==>
      lbalance_gt_tree k r ==>
      lbalance_bst l ==>
      lbalance_bst r ==>
      ((case l of
          LBalanceNode LBalanceRed
            (LBalanceNode LBalanceRed a kx vx b) ky vy c => T
        | LBalanceNode LBalanceRed a kx vx
            (LBalanceNode LBalanceRed b ky vy c) => T
        | _ => T) /\
       !result : lbalance_tree.
         (case l of
            LBalanceNode LBalanceRed
              (LBalanceNode LBalanceRed a kx vx b) ky vy c =>
                result =
                  LBalanceNode LBalanceRed
                    (LBalanceNode LBalanceBlack a kx vx b) ky vy
                    (LBalanceNode LBalanceBlack c k v r)
          | LBalanceNode LBalanceRed a kx vx
              (LBalanceNode LBalanceRed b ky vy c) =>
                result =
                  LBalanceNode LBalanceRed
                    (LBalanceNode LBalanceBlack a kx vx b) ky vy
                    (LBalanceNode LBalanceBlack c k v r)
          | _ =>
                result = LBalanceNode LBalanceBlack l k v r)
         ==>
         lbalance_bst result /\
         (!n : int.
            lbalance_almost_rbtree n l ==>
            lbalance_rbtree n r ==>
            lbalance_rbtree (n + (1 : int)) result) /\
         (!k' : int. !v' : int.
            lbalance_memt result k' v' <=>
              (if k' = k
               then v' = v
               else
                 lbalance_memt l k' v' \/
                 lbalance_memt r k' v')))``;

(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vacid_0_red_black_trees_Vacid0_removeqtvc: the remove verification
  condition for an integer-keyed red-black-tree map with a default value,
  preserving its invariant and universally quantified membership update.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  vacid_remove_color =
    VacidRemoveRed
  | VacidRemoveBlack
End

Datatype:
  vacid_remove_tree =
    VacidRemoveLeaf
  | VacidRemoveNode
      vacid_remove_color vacid_remove_tree int int vacid_remove_tree
End

val vacid_remove_memt_def = Define `
  (vacid_remove_memt VacidRemoveLeaf k v = F) /\
  (vacid_remove_memt
      (VacidRemoveNode color left key value right) k v =
     ((k = key /\ v = value) \/
      vacid_remove_memt left k v \/
      vacid_remove_memt right k v))`;

val vacid_remove_lt_tree_def = Define `
  vacid_remove_lt_tree x t <=>
    !k : int. !v : int.
      vacid_remove_memt t k v ==> k < x`;

val vacid_remove_gt_tree_def = Define `
  vacid_remove_gt_tree x t <=>
    !k : int. !v : int.
      vacid_remove_memt t k v ==> x < k`;

val vacid_remove_bst_def = Define `
  (vacid_remove_bst VacidRemoveLeaf = T) /\
  (vacid_remove_bst
      (VacidRemoveNode color left key value right) =
     (vacid_remove_bst left /\
      vacid_remove_bst right /\
      vacid_remove_lt_tree key left /\
      vacid_remove_gt_tree key right))`;

val vacid_remove_is_not_red_def = Define `
  (vacid_remove_is_not_red VacidRemoveLeaf = T) /\
  (vacid_remove_is_not_red
      (VacidRemoveNode VacidRemoveRed left key value right) = F) /\
  (vacid_remove_is_not_red
      (VacidRemoveNode VacidRemoveBlack left key value right) = T)`;

val vacid_remove_rbtree_def = Define `
  (vacid_remove_rbtree n VacidRemoveLeaf = (n = (0 : int))) /\
  (vacid_remove_rbtree n
      (VacidRemoveNode VacidRemoveRed left key value right) =
     (vacid_remove_rbtree n left /\
      vacid_remove_rbtree n right /\
      vacid_remove_is_not_red left /\
      vacid_remove_is_not_red right)) /\
  (vacid_remove_rbtree n
      (VacidRemoveNode VacidRemoveBlack left key value right) =
     (vacid_remove_rbtree (n - (1 : int)) left /\
      vacid_remove_rbtree (n - (1 : int)) right))`;

val vacid_remove_inv_def = Define `
  vacid_remove_inv (state : int # vacid_remove_tree) <=>
    vacid_remove_bst (SND state) /\
    (?n : int. vacid_remove_rbtree n (SND state))`;

val vacid_remove_default_def = Define `
  vacid_remove_default (state : int # vacid_remove_tree) =
    FST state`;

val vacid_remove_mem_def = Define `
  vacid_remove_mem
      (state : int # vacid_remove_tree) (k : int) (v : int) <=>
    vacid_remove_memt (SND state) k v \/
    (v = vacid_remove_default state /\
     (!v' : int. ~vacid_remove_memt (SND state) k v'))`;

val vacid_remove_post_def = Define `
  vacid_remove_post
      (m : int) (m1 : vacid_remove_tree) (k : int)
      (m2 : vacid_remove_tree) <=>
    vacid_remove_inv (m,m2) /\
    (!k' : int. !v' : int.
       vacid_remove_mem (m,m2) k' v' <=>
       (if k' = k
        then v' = m
        else vacid_remove_mem (m,m1) k' v'))`;

val vacid_0_red_black_trees_Vacid0_removeqtvc_statement =
  ``!(m : int) (m1 : vacid_remove_tree) (k : int).
      vacid_remove_inv (m,m1) ==>
      vacid_remove_inv (m,m1) /\
      (!m2 : vacid_remove_tree.
         vacid_remove_post m m1 k m2 ==>
         vacid_remove_post m m1 k m2)``;

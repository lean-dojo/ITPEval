(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vacid_0_red_black_trees_Vacid0_lookupqtvc: the lookup verification
  condition for an integer-keyed red-black-tree map with a default value,
  relating the tree invariant, key-value membership, key absence, and returned
  values. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  vacid_lookup_color =
    VacidLookupRed
  | VacidLookupBlack
End

Datatype:
  vacid_lookup_tree =
    VacidLookupLeaf
  | VacidLookupNode
      vacid_lookup_color vacid_lookup_tree int int vacid_lookup_tree
End

val vacid_lookup_memt_def = Define `
  (vacid_lookup_memt VacidLookupLeaf k v = F) /\
  (vacid_lookup_memt
      (VacidLookupNode color left key value right) k v =
     ((k = key /\ v = value) \/
      vacid_lookup_memt left k v \/
      vacid_lookup_memt right k v))`;

val vacid_lookup_lt_tree_def = Define `
  vacid_lookup_lt_tree x t <=>
    !k : int. !v : int.
      vacid_lookup_memt t k v ==> k < x`;

val vacid_lookup_gt_tree_def = Define `
  vacid_lookup_gt_tree x t <=>
    !k : int. !v : int.
      vacid_lookup_memt t k v ==> x < k`;

val vacid_lookup_bst_def = Define `
  (vacid_lookup_bst VacidLookupLeaf = T) /\
  (vacid_lookup_bst
      (VacidLookupNode color left key value right) =
     (vacid_lookup_bst left /\
      vacid_lookup_bst right /\
      vacid_lookup_lt_tree key left /\
      vacid_lookup_gt_tree key right))`;

val vacid_lookup_is_not_red_def = Define `
  (vacid_lookup_is_not_red VacidLookupLeaf = T) /\
  (vacid_lookup_is_not_red
      (VacidLookupNode VacidLookupRed left key value right) = F) /\
  (vacid_lookup_is_not_red
      (VacidLookupNode VacidLookupBlack left key value right) = T)`;

val vacid_lookup_rbtree_def = Define `
  (vacid_lookup_rbtree n VacidLookupLeaf = (n = (0 : int))) /\
  (vacid_lookup_rbtree n
      (VacidLookupNode VacidLookupRed left key value right) =
     (vacid_lookup_rbtree n left /\
      vacid_lookup_rbtree n right /\
      vacid_lookup_is_not_red left /\
      vacid_lookup_is_not_red right)) /\
  (vacid_lookup_rbtree n
      (VacidLookupNode VacidLookupBlack left key value right) =
     (vacid_lookup_rbtree (n - (1 : int)) left /\
      vacid_lookup_rbtree (n - (1 : int)) right))`;

val vacid_lookup_inv_def = Define `
  vacid_lookup_inv (state : int # vacid_lookup_tree) <=>
    vacid_lookup_bst (SND state) /\
    (?n : int. vacid_lookup_rbtree n (SND state))`;

val vacid_lookup_default_def = Define `
  vacid_lookup_default (state : int # vacid_lookup_tree) =
    FST state`;

val vacid_lookup_mem_def = Define `
  vacid_lookup_mem
      (state : int # vacid_lookup_tree) (k : int) (v : int) <=>
    vacid_lookup_memt (SND state) k v \/
    (v = vacid_lookup_default state /\
     (!v' : int. ~vacid_lookup_memt (SND state) k v'))`;

val vacid_0_red_black_trees_Vacid0_lookupqtvc_statement =
  ``!(m : int) (m1 : vacid_lookup_tree) (k : int).
      vacid_lookup_inv (m,m1) ==>
      vacid_lookup_bst m1 /\
      (!result : int.
         (vacid_lookup_memt m1 k result \/
          ((!v : int. ~vacid_lookup_memt m1 k v) /\
           result = m)) ==>
         vacid_lookup_mem (m,m1) k result)``;

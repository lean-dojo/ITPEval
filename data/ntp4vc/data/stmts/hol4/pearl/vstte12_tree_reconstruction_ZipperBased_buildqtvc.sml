(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vstte12_tree_reconstruction_ZipperBased_buildqtvc: the initial zipper
  invariant and the success/failure specification for reconstructing a finite
  binary tree from its mathematical-integer leaf-depth list. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  zbbq_tree =
    ZBBQLeaf
  | ZBBQNode zbbq_tree zbbq_tree
End

val zbbq_depths_def = Define `
  (zbbq_depths (d : int) ZBBQLeaf = [d]) /\
  (zbbq_depths d (ZBBQNode left right) =
     zbbq_depths (d + (1 : int)) left ++
     zbbq_depths (d + (1 : int)) right)`;

val zbbq_forest_depths_def = Define `
  (zbbq_forest_depths
      ([] : (int # zbbq_tree) list) = ([] : int list)) /\
  (zbbq_forest_depths (entry :: rest) =
     zbbq_depths (FST entry) (SND entry) ++
     zbbq_forest_depths rest)`;

val zbbq_greedy_def = Define `
  (zbbq_greedy (d : int) d1 ZBBQLeaf =
     (~(d = d1) /\ T)) /\
  (zbbq_greedy d d1 (ZBBQNode left right) =
     (~(d = d1) /\
      zbbq_greedy d (d1 + (1 : int)) left))`;

val (zbbq_g_rules, zbbq_g_ind, zbbq_g_cases) =
  Hol_reln `
    zbbq_g ([] : (int # zbbq_tree) list) /\
    (!d t.
       zbbq_g [((d : int), (t : zbbq_tree))]) /\
    (!d1 d2 t2 t1 l.
       zbbq_greedy d1 d2 t2 /\
       zbbq_g ((d1, t1) :: l) ==>
       zbbq_g ((d2, t2) :: (d1, t1) :: l))
  `;

val zbbq_only_leaf_def = Define `
  (zbbq_only_leaf
      ([] : (int # zbbq_tree) list) = T) /\
  (zbbq_only_leaf (entry :: rest) =
     (SND entry = ZBBQLeaf /\ zbbq_only_leaf rest))`;

val zbbq_map_leaf_def = Define `
  (zbbq_map_leaf ([] : int list) =
     ([] : (int # zbbq_tree) list)) /\
  (zbbq_map_leaf (d :: rest) =
     (d, ZBBQLeaf) :: zbbq_map_leaf rest)`;

val vstte12_tree_reconstruction_ZipperBased_buildqtvc_statement =
  ``!s : int list.
      let o1 = zbbq_map_leaf s in
      let o2 = ([] : (int # zbbq_tree) list) in
        (zbbq_g o2 /\
         (case o1 of
            [] => T
          | entry :: right_tail =>
              zbbq_only_leaf right_tail /\
              (case SND entry of
                 ZBBQLeaf => T
               | ZBBQNode left right =>
                   zbbq_g
                     ((FST entry + (1 : int), left) :: o2)))) /\
        (!result : zbbq_tree.
           zbbq_depths (0 : int) result =
             zbbq_forest_depths (REVERSE o2 ++ o1) ==>
           zbbq_depths (0 : int) result = s) /\
        ((!t : zbbq_tree.
            ~(zbbq_depths (0 : int) t =
              zbbq_forest_depths (REVERSE o2 ++ o1))) ==>
         (!t : zbbq_tree.
            ~(zbbq_depths (0 : int) t = s)))``;

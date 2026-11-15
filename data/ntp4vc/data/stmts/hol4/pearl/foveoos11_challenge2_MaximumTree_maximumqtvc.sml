(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/foveoos11_challenge2_MaximumTree_maximumqtvc: a verification
  condition for computing the greatest integer label in a nonempty binary
  tree, including recursive size obligations and maximum correctness. This
  file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  maximum_tree_tree =
    MaximumTreeEmpty
  | MaximumTreeNode maximum_tree_tree int maximum_tree_tree
End

val maximum_tree_size_def = Define `
  (maximum_tree_size MaximumTreeEmpty = (0 : int)) /\
  (maximum_tree_size (MaximumTreeNode l x r) =
     (1 : int) + maximum_tree_size l + maximum_tree_size r)`;

val maximum_tree_mem_def = Define `
  (maximum_tree_mem (x : int) MaximumTreeEmpty = F) /\
  (maximum_tree_mem x (MaximumTreeNode l v r) =
     (maximum_tree_mem x l \/ x = v \/ maximum_tree_mem x r))`;

val maximum_tree_max_def = Define `
  maximum_tree_max (x : int) y = if x < y then y else x`;

val foveoos11_challenge2_MaximumTree_maximum_vc =
  ``!(t : maximum_tree_tree).
      ~(t = MaximumTreeEmpty) ==>
      ((case t of
          MaximumTreeEmpty => F
        | MaximumTreeNode MaximumTreeEmpty v MaximumTreeEmpty => T
        | MaximumTreeNode MaximumTreeEmpty v s =>
            (((0 : int) <= maximum_tree_size t /\
              maximum_tree_size s < maximum_tree_size t) /\
             ~(s = MaximumTreeEmpty))
        | MaximumTreeNode s v MaximumTreeEmpty =>
            (((0 : int) <= maximum_tree_size t /\
              maximum_tree_size s < maximum_tree_size t) /\
             ~(s = MaximumTreeEmpty))
        | MaximumTreeNode l v r =>
            ((((0 : int) <= maximum_tree_size t /\
               maximum_tree_size r < maximum_tree_size t) /\
              ~(r = MaximumTreeEmpty)) /\
             !o1 : int.
               maximum_tree_mem o1 r /\
               (!x : int.
                  maximum_tree_mem x r ==> x <= o1)
               ==>
               (((0 : int) <= maximum_tree_size t /\
                 maximum_tree_size l < maximum_tree_size t) /\
                ~(l = MaximumTreeEmpty)))) /\
       !result : int.
         (case t of
            MaximumTreeEmpty => F
          | MaximumTreeNode MaximumTreeEmpty v MaximumTreeEmpty =>
              result = v
          | MaximumTreeNode MaximumTreeEmpty v s =>
              ?o1 : int.
                (maximum_tree_mem o1 s /\
                 (!x : int.
                    maximum_tree_mem x s ==> x <= o1)) /\
                result = maximum_tree_max o1 v
          | MaximumTreeNode s v MaximumTreeEmpty =>
              ?o1 : int.
                (maximum_tree_mem o1 s /\
                 (!x : int.
                    maximum_tree_mem x s ==> x <= o1)) /\
                result = maximum_tree_max o1 v
          | MaximumTreeNode l v r =>
              ?o1 : int.
                (maximum_tree_mem o1 r /\
                 (!x : int.
                    maximum_tree_mem x r ==> x <= o1)) /\
                ?o2 : int.
                  (maximum_tree_mem o2 l /\
                   (!x : int.
                      maximum_tree_mem x l ==> x <= o2)) /\
                  result =
                    maximum_tree_max o2
                      (maximum_tree_max v o1))
         ==>
         maximum_tree_mem result t /\
         !x : int.
           maximum_tree_mem x t ==> x <= result)``;

(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/tree_height_HeightStack_height_stackqtvc: the explicit-stack tree
  height verification condition, combining lexicographic recursive-call
  decrease obligations with the accumulator-and-stack height result. This
  file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  tree_height_tree =
    TreeHeightEmpty
  | TreeHeightNode tree_height_tree 'a tree_height_tree
End

val tree_height_max_def = Define `
  tree_height_max (x : int) y =
    if x < y then y else x`;

val tree_height_size_def = Define `
  (tree_height_size
      (TreeHeightEmpty : 'a tree_height_tree) = (0 : int)) /\
  (tree_height_size (TreeHeightNode l x r) =
     (1 : int) + tree_height_size l + tree_height_size r)`;

val tree_height_height_def = Define `
  (tree_height_height
      (TreeHeightEmpty : 'a tree_height_tree) = (0 : int)) /\
  (tree_height_height (TreeHeightNode l x r) =
     (1 : int) +
       tree_height_max
         (tree_height_height l)
         (tree_height_height r))`;

val tree_height_heights_def = Define `
  (tree_height_heights
      ([] : (int # 'a tree_height_tree) list) = (0 : int)) /\
  (tree_height_heights ((h, t)::s') =
     tree_height_max
       (h + tree_height_height t)
       (tree_height_heights s'))`;

val tree_height_sizes_def = Define `
  (tree_height_sizes
      ([] : (int # 'a tree_height_tree) list) = (0 : int)) /\
  (tree_height_sizes ((h, t)::s') =
     tree_height_size t + tree_height_sizes s')`;

val tree_height_HeightStack_height_stackqtvc_statement =
  ``!(m : int) (s : (int # 'a tree_height_tree) list).
      (0 : int) <= m ==>
      ((case s of
          [] => T
        | (h, TreeHeightEmpty)::s' =>
            (((0 : int) <= tree_height_sizes s /\
              tree_height_sizes s' < tree_height_sizes s) \/
             (tree_height_sizes s = tree_height_sizes s' /\
              (case s of
                 [] => F
               | x::f => f = s'))) /\
            (0 : int) <= tree_height_max m h
        | (h, TreeHeightNode l x r)::s' =>
            let o1 =
              (h + (1 : int), l)::
                (h + (1 : int), r)::s'
            in
              (((0 : int) <= tree_height_sizes s /\
                tree_height_sizes o1 < tree_height_sizes s) \/
               (tree_height_sizes s = tree_height_sizes o1 /\
                (case s of
                   [] => F
                 | x::f => f = o1))) /\
              (0 : int) <= m) /\
       (!result : int.
          (case s of
             [] => result = m
           | (h, TreeHeightEmpty)::s' =>
               result =
                 tree_height_max
                   (tree_height_max m h)
                   (tree_height_heights s')
           | (h, TreeHeightNode l x r)::s' =>
               result =
                 tree_height_max
                   m
                   (tree_height_heights
                     ((h + (1 : int), l)::
                       (h + (1 : int), r)::s')))
          ==>
          result =
            tree_height_max m (tree_height_heights s)))``;

(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/tree_height_Iteration_height1qtvc: the iterative tree-height
  verification condition for an explicit continuation and work item,
  including loop initialization, invariant preservation, variant decrease,
  and final-result extraction. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

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

Datatype:
  tree_height_iteration_cont =
    TreeHeightIterationId
  | TreeHeightIterationKleft
      ('a tree_height_tree)
      tree_height_iteration_cont
  | TreeHeightIterationKright
      int
      tree_height_iteration_cont
End

Datatype:
  tree_height_iteration_what =
    TreeHeightIterationArgument ('a tree_height_tree)
  | TreeHeightIterationResult int
End

val tree_height_iteration_is_id_def = Define `
  (tree_height_iteration_is_id
      (TreeHeightIterationId :
        'a tree_height_iteration_cont) = T) /\
  (tree_height_iteration_is_id
      (TreeHeightIterationKleft t k) = F) /\
  (tree_height_iteration_is_id
      (TreeHeightIterationKright x k) = F)`;

val tree_height_iteration_is_result_def = Define `
  (tree_height_iteration_is_result
      (TreeHeightIterationArgument t) = F) /\
  (tree_height_iteration_is_result
      (TreeHeightIterationResult x :
        'a tree_height_iteration_what) = T)`;

val tree_height_iteration_evalk_def = Define `
  (tree_height_iteration_evalk
      (TreeHeightIterationId :
        'a tree_height_iteration_cont)
      r = r) /\
  (tree_height_iteration_evalk
      (TreeHeightIterationKleft l k)
      r =
     tree_height_iteration_evalk
       k
       ((1 : int) +
        tree_height_max (tree_height_height l) r)) /\
  (tree_height_iteration_evalk
      (TreeHeightIterationKright x k)
      r =
     tree_height_iteration_evalk
       k
       ((1 : int) + tree_height_max x r))`;

val tree_height_iteration_evalw_def = Define `
  (tree_height_iteration_evalw
      (TreeHeightIterationArgument t) =
     tree_height_height t) /\
  (tree_height_iteration_evalw
      (TreeHeightIterationResult x :
        'a tree_height_iteration_what) = x)`;

val tree_height_iteration_sizek_def = Define `
  (tree_height_iteration_sizek
      (TreeHeightIterationId :
        'a tree_height_iteration_cont) = (0 : int)) /\
  (tree_height_iteration_sizek
      (TreeHeightIterationKleft t k) =
     (3 : int) +
       (4 : int) * tree_height_size t +
       tree_height_iteration_sizek k) /\
  (tree_height_iteration_sizek
      (TreeHeightIterationKright x k) =
     (1 : int) + tree_height_iteration_sizek k)`;

val tree_height_iteration_sizew_def = Define `
  (tree_height_iteration_sizew
      (TreeHeightIterationArgument t) =
     (1 : int) + (4 : int) * tree_height_size t) /\
  (tree_height_iteration_sizew
      (TreeHeightIterationResult x :
        'a tree_height_iteration_what) = (0 : int))`;

val tree_height_iteration_step_obligation_def = Define `
  tree_height_iteration_step_obligation
    (t : 'a tree_height_tree)
    (k : 'a tree_height_iteration_cont)
    (w : 'a tree_height_iteration_what) =
    case k of
      TreeHeightIterationId =>
        (case w of
           TreeHeightIterationArgument x =>
             (case x of
                TreeHeightEmpty =>
                  (((0 : int) <=
                      tree_height_iteration_sizek k +
                      tree_height_iteration_sizew w /\
                    tree_height_iteration_sizek k +
                      tree_height_iteration_sizew
                        (TreeHeightIterationResult (0 : int) :
                          'a tree_height_iteration_what) <
                    tree_height_iteration_sizek k +
                      tree_height_iteration_sizew w) /\
                   tree_height_iteration_evalk
                     k
                     (tree_height_iteration_evalw
                       (TreeHeightIterationResult (0 : int) :
                         'a tree_height_iteration_what)) =
                   tree_height_height t)
              | TreeHeightNode x1 x2 x3 =>
                  (((0 : int) <=
                      tree_height_iteration_sizek k +
                      tree_height_iteration_sizew w /\
                    tree_height_iteration_sizek
                        (TreeHeightIterationKleft x3 k) +
                      tree_height_iteration_sizew
                        (TreeHeightIterationArgument x1) <
                    tree_height_iteration_sizek k +
                      tree_height_iteration_sizew w) /\
                   tree_height_iteration_evalk
                     (TreeHeightIterationKleft x3 k)
                     (tree_height_iteration_evalw
                       (TreeHeightIterationArgument x1)) =
                   tree_height_height t))
         | TreeHeightIterationResult x => F)
    | TreeHeightIterationKleft x k1 =>
        (case w of
           TreeHeightIterationArgument x2 =>
             (case x2 of
                TreeHeightEmpty =>
                  (((0 : int) <=
                      tree_height_iteration_sizek k +
                      tree_height_iteration_sizew w /\
                    tree_height_iteration_sizek k +
                      tree_height_iteration_sizew
                        (TreeHeightIterationResult (0 : int) :
                          'a tree_height_iteration_what) <
                    tree_height_iteration_sizek k +
                      tree_height_iteration_sizew w) /\
                   tree_height_iteration_evalk
                     k
                     (tree_height_iteration_evalw
                       (TreeHeightIterationResult (0 : int) :
                         'a tree_height_iteration_what)) =
                   tree_height_height t)
              | TreeHeightNode x3 x4 x5 =>
                  (((0 : int) <=
                      tree_height_iteration_sizek k +
                      tree_height_iteration_sizew w /\
                    tree_height_iteration_sizek
                        (TreeHeightIterationKleft x5 k) +
                      tree_height_iteration_sizew
                        (TreeHeightIterationArgument x3) <
                    tree_height_iteration_sizek k +
                      tree_height_iteration_sizew w) /\
                   tree_height_iteration_evalk
                     (TreeHeightIterationKleft x5 k)
                     (tree_height_iteration_evalw
                       (TreeHeightIterationArgument x3)) =
                   tree_height_height t))
         | TreeHeightIterationResult x2 =>
             (((0 : int) <=
                 tree_height_iteration_sizek k +
                 tree_height_iteration_sizew w /\
               tree_height_iteration_sizek
                   (TreeHeightIterationKright x2 k1) +
                 tree_height_iteration_sizew
                   (TreeHeightIterationArgument x) <
               tree_height_iteration_sizek k +
                 tree_height_iteration_sizew w) /\
              tree_height_iteration_evalk
                (TreeHeightIterationKright x2 k1)
                (tree_height_iteration_evalw
                  (TreeHeightIterationArgument x)) =
              tree_height_height t))
    | TreeHeightIterationKright x k1 =>
        (case w of
           TreeHeightIterationArgument x2 =>
             (case x2 of
                TreeHeightEmpty =>
                  (((0 : int) <=
                      tree_height_iteration_sizek k +
                      tree_height_iteration_sizew w /\
                    tree_height_iteration_sizek k +
                      tree_height_iteration_sizew
                        (TreeHeightIterationResult (0 : int) :
                          'a tree_height_iteration_what) <
                    tree_height_iteration_sizek k +
                      tree_height_iteration_sizew w) /\
                   tree_height_iteration_evalk
                     k
                     (tree_height_iteration_evalw
                       (TreeHeightIterationResult (0 : int) :
                         'a tree_height_iteration_what)) =
                   tree_height_height t)
              | TreeHeightNode x3 x4 x5 =>
                  (((0 : int) <=
                      tree_height_iteration_sizek k +
                      tree_height_iteration_sizew w /\
                    tree_height_iteration_sizek
                        (TreeHeightIterationKleft x5 k) +
                      tree_height_iteration_sizew
                        (TreeHeightIterationArgument x3) <
                    tree_height_iteration_sizek k +
                      tree_height_iteration_sizew w) /\
                   tree_height_iteration_evalk
                     (TreeHeightIterationKleft x5 k)
                     (tree_height_iteration_evalw
                       (TreeHeightIterationArgument x3)) =
                   tree_height_height t))
         | TreeHeightIterationResult x2 =>
             let next_result =
               (TreeHeightIterationResult
                  ((1 : int) + tree_height_max x x2) :
                'a tree_height_iteration_what)
             in
               (((0 : int) <=
                   tree_height_iteration_sizek k +
                   tree_height_iteration_sizew w /\
                 tree_height_iteration_sizek k1 +
                   tree_height_iteration_sizew next_result <
                 tree_height_iteration_sizek k +
                   tree_height_iteration_sizew w) /\
                tree_height_iteration_evalk
                  k1
                  (tree_height_iteration_evalw next_result) =
                tree_height_height t))`;

val tree_height_iteration_final_obligation_def = Define `
  tree_height_iteration_final_obligation
    (t : 'a tree_height_tree)
    (w : 'a tree_height_iteration_what) =
    ((case w of
        TreeHeightIterationArgument x => F
      | TreeHeightIterationResult r => T) /\
     (!result : int.
        (case w of
           TreeHeightIterationArgument x => F
         | TreeHeightIterationResult r => result = r)
        ==>
        result = tree_height_height t))`;

val tree_height_Iteration_height1qtvc_statement =
  ``!(t : 'a tree_height_tree).
      tree_height_iteration_evalk
        (TreeHeightIterationId :
          'a tree_height_iteration_cont)
        (tree_height_iteration_evalw
          (TreeHeightIterationArgument t)) =
        tree_height_height t /\
      !(k : 'a tree_height_iteration_cont)
       (w : 'a tree_height_iteration_what).
        tree_height_iteration_evalk
          k
          (tree_height_iteration_evalw w) =
          tree_height_height t
        ==>
        !o1 : bool.
          (if tree_height_iteration_is_id k then
             o1 =
               (if tree_height_iteration_is_result w
                then T
                else F)
           else
             o1 = F)
          ==>
          if ~(o1 = T) then
            tree_height_iteration_step_obligation t k w
          else
            tree_height_iteration_final_obligation t w``;

(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/braun_trees_BraunHeaps_addqtvc: a Braun-heap insertion verification
  condition preserving heap order, the Braun size invariant, element
  multiplicities, and total size. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  braun_add_tree =
    BraunAddEmpty
  | BraunAddNode braun_add_tree 'elt braun_add_tree
End

val braun_add_size_def = Define `
  (braun_add_size (BraunAddEmpty : 'elt braun_add_tree) = (0 : int)) /\
  (braun_add_size (BraunAddNode l x r) =
     (1 : int) + braun_add_size l + braun_add_size r)`;

val braun_add_occ_def = Define `
  (braun_add_occ x (BraunAddEmpty : 'elt braun_add_tree) = (0 : int)) /\
  (braun_add_occ x (BraunAddNode l y r) =
     (if y = x then (1 : int) else (0 : int)) +
       braun_add_occ x l + braun_add_occ x r)`;

val braun_add_le_root_def = Define `
  (braun_add_le_root le e
      (BraunAddEmpty : 'elt braun_add_tree) = T) /\
  (braun_add_le_root le e (BraunAddNode l x r) = le e x)`;

val braun_add_heap_def = Define `
  (braun_add_heap le
      (BraunAddEmpty : 'elt braun_add_tree) = T) /\
  (braun_add_heap le (BraunAddNode l x r) =
     (braun_add_le_root le x l /\
      braun_add_heap le l /\
      braun_add_le_root le x r /\
      braun_add_heap le r))`;

val braun_add_inv_def = Define `
  (braun_add_inv (BraunAddEmpty : 'elt braun_add_tree) = T) /\
  (braun_add_inv (BraunAddNode l x r) =
     ((braun_add_size l = braun_add_size r \/
       braun_add_size l = braun_add_size r + (1 : int)) /\
      braun_add_inv l /\
      braun_add_inv r))`;

val braun_trees_BraunHeaps_add_vc =
  ``!(le : 'elt -> 'elt -> bool)
      (t : 'elt braun_add_tree)
      (x : 'elt).
      (!u. le u u) ==>
      (!u v w. le u v /\ le v w ==> le u w) ==>
      (!u v. le u v \/ le v u) ==>
      braun_add_heap le t ==>
      braun_add_inv t ==>
      ((case t of
          BraunAddEmpty => T
        | BraunAddNode l y r =>
            (case t of
               BraunAddEmpty => F
             | BraunAddNode f z f1 => f = r \/ f1 = r) /\
            braun_add_heap le r /\
            braun_add_inv r) /\
       !result.
         (case t of
            BraunAddEmpty =>
              result =
                BraunAddNode BraunAddEmpty x BraunAddEmpty
          | BraunAddNode l y r =>
              if le x y
              then
                ?o1.
                  (braun_add_heap le o1 /\
                   braun_add_inv o1 /\
                   braun_add_occ y o1 =
                     braun_add_occ y r + (1 : int) /\
                   (!e.
                      ~(e = y) ==>
                      braun_add_occ e o1 = braun_add_occ e r) /\
                   braun_add_size o1 =
                     braun_add_size r + (1 : int)) /\
                  result = BraunAddNode o1 x l
              else
                ?o1.
                  (braun_add_heap le o1 /\
                   braun_add_inv o1 /\
                   braun_add_occ x o1 =
                     braun_add_occ x r + (1 : int) /\
                   (!e.
                      ~(e = x) ==>
                      braun_add_occ e o1 = braun_add_occ e r) /\
                   braun_add_size o1 =
                     braun_add_size r + (1 : int)) /\
                  result = BraunAddNode o1 y l)
         ==>
         braun_add_heap le result /\
         braun_add_inv result /\
         braun_add_occ x result =
           braun_add_occ x t + (1 : int) /\
         (!e.
            ~(e = x) ==>
            braun_add_occ e result = braun_add_occ e t) /\
         braun_add_size result =
           braun_add_size t + (1 : int))``;

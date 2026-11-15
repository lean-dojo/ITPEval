(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/braun_trees_BraunHeaps_extractqtvc: a Braun-heap extraction
  verification condition preserving heap order, the Braun size invariant,
  total size, and element multiplicities. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  braun_extract_tree =
    BraunExtractEmpty
  | BraunExtractNode braun_extract_tree 'elt braun_extract_tree
End

val braun_extract_size_def = Define `
  (braun_extract_size
      (BraunExtractEmpty : 'elt braun_extract_tree) = (0 : int)) /\
  (braun_extract_size (BraunExtractNode l x r) =
     (1 : int) + braun_extract_size l + braun_extract_size r)`;

val braun_extract_occ_def = Define `
  (braun_extract_occ x
      (BraunExtractEmpty : 'elt braun_extract_tree) = (0 : int)) /\
  (braun_extract_occ x (BraunExtractNode l y r) =
     (if y = x then (1 : int) else (0 : int)) +
       braun_extract_occ x l + braun_extract_occ x r)`;

val braun_extract_le_root_def = Define `
  (braun_extract_le_root le e
      (BraunExtractEmpty : 'elt braun_extract_tree) = T) /\
  (braun_extract_le_root le e (BraunExtractNode l x r) = le e x)`;

val braun_extract_heap_def = Define `
  (braun_extract_heap le
      (BraunExtractEmpty : 'elt braun_extract_tree) = T) /\
  (braun_extract_heap le (BraunExtractNode l x r) =
     (braun_extract_le_root le x l /\
      braun_extract_heap le l /\
      braun_extract_le_root le x r /\
      braun_extract_heap le r))`;

val braun_extract_inv_def = Define `
  (braun_extract_inv
      (BraunExtractEmpty : 'elt braun_extract_tree) = T) /\
  (braun_extract_inv (BraunExtractNode l x r) =
     ((braun_extract_size l = braun_extract_size r \/
       braun_extract_size l = braun_extract_size r + (1 : int)) /\
      braun_extract_inv l /\
      braun_extract_inv r))`;

val braun_trees_BraunHeaps_extract_vc =
  ``!(le : 'elt -> 'elt -> bool)
      (t : 'elt braun_extract_tree).
      (!x. le x x) ==>
      (!x y z. le x y /\ le y z ==> le x z) ==>
      (!x y. le x y \/ le y x) ==>
      braun_extract_heap le t ==>
      braun_extract_inv t ==>
      (0 : int) < braun_extract_size t ==>
      ((case t of
          BraunExtractEmpty => F
        | BraunExtractNode BraunExtractEmpty y r => T
        | BraunExtractNode l y r =>
            (case t of
               BraunExtractEmpty => F
             | BraunExtractNode f z f1 => f = l \/ f1 = l) /\
            braun_extract_heap le l /\
            braun_extract_inv l /\
            (0 : int) < braun_extract_size l) /\
       !e t'.
         (case t of
            BraunExtractEmpty => F
          | BraunExtractNode BraunExtractEmpty y r =>
              e = y /\ t' = BraunExtractEmpty
          | BraunExtractNode l y r =>
              ?t1.
                (braun_extract_heap le t1 /\
                 braun_extract_inv t1 /\
                 braun_extract_size t1 =
                   braun_extract_size l - (1 : int) /\
                 braun_extract_occ e t1 =
                   braun_extract_occ e l - (1 : int) /\
                 (!x.
                    ~(x = e) ==>
                    braun_extract_occ x t1 =
                      braun_extract_occ x l)) /\
                t' = BraunExtractNode r y t1)
         ==>
         braun_extract_heap le t' /\
         braun_extract_inv t' /\
         braun_extract_size t' =
           braun_extract_size t - (1 : int) /\
         braun_extract_occ e t' =
           braun_extract_occ e t - (1 : int) /\
         !x.
           ~(x = e) ==>
           braun_extract_occ x t' =
             braun_extract_occ x t)``;

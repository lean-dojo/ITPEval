(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/braun_trees_BraunHeaps_mergeqtvc: a Braun-heap merge verification
  condition preserving heap order, the Braun size invariant, element
  multiplicities, and total size. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  braun_merge_tree =
    BraunMergeEmpty
  | BraunMergeNode braun_merge_tree 'elt braun_merge_tree
End

val braun_merge_size_def = Define `
  (braun_merge_size
      (BraunMergeEmpty : 'elt braun_merge_tree) = (0 : int)) /\
  (braun_merge_size (BraunMergeNode l x r) =
     (1 : int) + braun_merge_size l + braun_merge_size r)`;

val braun_merge_occ_def = Define `
  (braun_merge_occ x
      (BraunMergeEmpty : 'elt braun_merge_tree) = (0 : int)) /\
  (braun_merge_occ x (BraunMergeNode l y r) =
     (if y = x then (1 : int) else (0 : int)) +
       braun_merge_occ x l + braun_merge_occ x r)`;

val braun_merge_le_root_def = Define `
  (braun_merge_le_root le e
      (BraunMergeEmpty : 'elt braun_merge_tree) = T) /\
  (braun_merge_le_root le e (BraunMergeNode l x r) = le e x)`;

val braun_merge_heap_def = Define `
  (braun_merge_heap le
      (BraunMergeEmpty : 'elt braun_merge_tree) = T) /\
  (braun_merge_heap le (BraunMergeNode l x r) =
     (braun_merge_le_root le x l /\
      braun_merge_heap le l /\
      braun_merge_le_root le x r /\
      braun_merge_heap le r))`;

val braun_merge_inv_def = Define `
  (braun_merge_inv
      (BraunMergeEmpty : 'elt braun_merge_tree) = T) /\
  (braun_merge_inv (BraunMergeNode l x r) =
     ((braun_merge_size l = braun_merge_size r \/
       braun_merge_size l = braun_merge_size r + (1 : int)) /\
      braun_merge_inv l /\
      braun_merge_inv r))`;

val braun_trees_BraunHeaps_merge_vc =
  ``!(le : 'elt -> 'elt -> bool)
      (minimum : 'elt braun_merge_tree -> 'elt)
      (l : 'elt braun_merge_tree)
      (r : 'elt braun_merge_tree).
      (!x. le x x) ==>
      (!x y z. le x y /\ le y z ==> le x z) ==>
      (!x y. le x y \/ le y x) ==>
      (!left x right.
         minimum (BraunMergeNode left x right) = x) ==>
      braun_merge_heap le l ==>
      braun_merge_heap le r ==>
      braun_merge_inv l ==>
      braun_merge_inv r ==>
      braun_merge_size r <= braun_merge_size l ==>
      braun_merge_size l <= braun_merge_size r + (1 : int) ==>
      ((case r of
          BraunMergeEmpty =>
            (case l of
               BraunMergeEmpty => T
             | _ => T)
        | BraunMergeNode x x1 x2 =>
            (case l of
               BraunMergeEmpty => F
             | BraunMergeNode x3 x4 x5 =>
                 if le x4 x1
                 then
                   ((0 : int) <=
                      braun_merge_size l + braun_merge_size r /\
                    braun_merge_size x3 + braun_merge_size x5 <
                      braun_merge_size l + braun_merge_size r) /\
                   (braun_merge_heap le x3 /\
                    braun_merge_heap le x5) /\
                   (braun_merge_inv x3 /\
                    braun_merge_inv x5) /\
                   braun_merge_size x5 <= braun_merge_size x3 /\
                   braun_merge_size x3 <=
                     braun_merge_size x5 + (1 : int)
                 else
                   (braun_merge_heap le l /\
                    braun_merge_inv l /\
                    (0 : int) < braun_merge_size l) /\
                   !x6 l1.
                     braun_merge_heap le l1 /\
                     braun_merge_inv l1 /\
                     braun_merge_size l1 =
                       braun_merge_size l - (1 : int) /\
                     braun_merge_occ x6 l1 =
                       braun_merge_occ x6 l - (1 : int) /\
                     (!x7.
                        ~(x7 = x6) ==>
                        braun_merge_occ x7 l1 =
                          braun_merge_occ x7 l)
                     ==>
                     braun_merge_heap le r /\
                     braun_merge_inv r /\
                     (0 : int) < braun_merge_size r)) /\
       !result.
         (case r of
            BraunMergeEmpty =>
              (case l of
                 BraunMergeEmpty => result = l
               | _ => result = l)
          | BraunMergeNode x x1 x2 =>
              (case l of
                 BraunMergeEmpty => F
               | BraunMergeNode x3 x4 x5 =>
                   if le x4 x1
                   then
                     ?o1.
                       (braun_merge_heap le o1 /\
                        braun_merge_inv o1 /\
                        (!e.
                           braun_merge_occ e o1 =
                             braun_merge_occ e x3 +
                               braun_merge_occ e x5) /\
                        braun_merge_size o1 =
                          braun_merge_size x3 +
                            braun_merge_size x5) /\
                       result = BraunMergeNode r x4 o1
                   else
                     ?e t'.
                       (braun_merge_heap le t' /\
                        braun_merge_inv t' /\
                        braun_merge_size t' =
                          braun_merge_size l - (1 : int) /\
                        braun_merge_occ e t' =
                          braun_merge_occ e l - (1 : int) /\
                        (!x6.
                           ~(x6 = e) ==>
                           braun_merge_occ x6 t' =
                             braun_merge_occ x6 l)) /\
                       (?o1.
                          (braun_merge_heap le o1 /\
                           braun_merge_inv o1 /\
                           (if e = minimum r
                            then
                              braun_merge_occ e o1 =
                                braun_merge_occ e r
                            else
                              braun_merge_occ e o1 =
                                braun_merge_occ e r + (1 : int) /\
                              braun_merge_occ (minimum r) o1 =
                                braun_merge_occ (minimum r) r -
                                  (1 : int)) /\
                           (!e1.
                              ~(e1 = e) ==>
                              ~(e1 = minimum r) ==>
                              braun_merge_occ e1 o1 =
                                braun_merge_occ e1 r) /\
                           braun_merge_size o1 =
                             braun_merge_size r) /\
                          result = BraunMergeNode o1 x1 t')))
         ==>
         braun_merge_heap le result /\
         braun_merge_inv result /\
         (!e.
            braun_merge_occ e result =
              braun_merge_occ e l + braun_merge_occ e r) /\
         braun_merge_size result =
           braun_merge_size l + braun_merge_size r)``;

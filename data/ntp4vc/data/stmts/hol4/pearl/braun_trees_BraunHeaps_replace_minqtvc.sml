(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/braun_trees_BraunHeaps_replace_minqtvc: a Braun-heap minimum
  replacement verification condition preserving heap order, the Braun size
  invariant, element multiplicities, and total size. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  braun_replace_min_tree =
    BraunReplaceMinEmpty
  | BraunReplaceMinNode braun_replace_min_tree 'elt braun_replace_min_tree
End

val braun_replace_min_size_def = Define `
  (braun_replace_min_size
      (BraunReplaceMinEmpty : 'elt braun_replace_min_tree) = (0 : int)) /\
  (braun_replace_min_size (BraunReplaceMinNode l x r) =
     (1 : int) + braun_replace_min_size l + braun_replace_min_size r)`;

val braun_replace_min_occ_def = Define `
  (braun_replace_min_occ x
      (BraunReplaceMinEmpty : 'elt braun_replace_min_tree) = (0 : int)) /\
  (braun_replace_min_occ x (BraunReplaceMinNode l y r) =
     (if y = x then (1 : int) else (0 : int)) +
       braun_replace_min_occ x l + braun_replace_min_occ x r)`;

val braun_replace_min_le_root_def = Define `
  (braun_replace_min_le_root le e
      (BraunReplaceMinEmpty : 'elt braun_replace_min_tree) = T) /\
  (braun_replace_min_le_root le e (BraunReplaceMinNode l x r) = le e x)`;

val braun_replace_min_heap_def = Define `
  (braun_replace_min_heap le
      (BraunReplaceMinEmpty : 'elt braun_replace_min_tree) = T) /\
  (braun_replace_min_heap le (BraunReplaceMinNode l x r) =
     (braun_replace_min_le_root le x l /\
      braun_replace_min_heap le l /\
      braun_replace_min_le_root le x r /\
      braun_replace_min_heap le r))`;

val braun_replace_min_inv_def = Define `
  (braun_replace_min_inv
      (BraunReplaceMinEmpty : 'elt braun_replace_min_tree) = T) /\
  (braun_replace_min_inv (BraunReplaceMinNode l x r) =
     ((braun_replace_min_size l = braun_replace_min_size r \/
       braun_replace_min_size l =
         braun_replace_min_size r + (1 : int)) /\
      braun_replace_min_inv l /\
      braun_replace_min_inv r))`;

val braun_trees_BraunHeaps_replace_min_vc =
  ``!(le : 'elt -> 'elt -> bool)
      (minimum : 'elt braun_replace_min_tree -> 'elt)
      (t : 'elt braun_replace_min_tree)
      (x : 'elt).
      (!u. le u u) ==>
      (!u v w. le u v /\ le v w ==> le u w) ==>
      (!u v. le u v \/ le v u) ==>
      (!left y right.
         minimum (BraunReplaceMinNode left y right) = y) ==>
      braun_replace_min_heap le t ==>
      braun_replace_min_inv t ==>
      (0 : int) < braun_replace_min_size t ==>
      ((case t of
          BraunReplaceMinEmpty => F
        | BraunReplaceMinNode l y r =>
            !o1.
              (if braun_replace_min_le_root le x l
               then
                 o1 =
                   (if braun_replace_min_le_root le x r
                    then T
                    else F)
               else o1 = F)
              ==>
              ~(o1 = T)
              ==>
              (braun_replace_min_heap le l /\
               (0 : int) < braun_replace_min_size l) /\
              (if braun_replace_min_le_root le (minimum l) r
               then
                 (case t of
                    BraunReplaceMinEmpty => F
                  | BraunReplaceMinNode f z f1 =>
                      f = l \/ f1 = l) /\
                 braun_replace_min_heap le l /\
                 braun_replace_min_inv l /\
                 (0 : int) < braun_replace_min_size l
               else
                 ((case t of
                     BraunReplaceMinEmpty => F
                   | BraunReplaceMinNode f z f1 =>
                       f = r \/ f1 = r) /\
                  braun_replace_min_heap le r /\
                  braun_replace_min_inv r /\
                  (0 : int) < braun_replace_min_size r) /\
                 !o2.
                   braun_replace_min_heap le o2 /\
                   braun_replace_min_inv o2 /\
                   (if x = minimum r
                    then
                      braun_replace_min_occ x o2 =
                        braun_replace_min_occ x r
                    else
                      braun_replace_min_occ x o2 =
                        braun_replace_min_occ x r + (1 : int) /\
                      braun_replace_min_occ (minimum r) o2 =
                        braun_replace_min_occ (minimum r) r - (1 : int)) /\
                   (!e.
                      ~(e = x) ==>
                      ~(e = minimum r) ==>
                      braun_replace_min_occ e o2 =
                        braun_replace_min_occ e r) /\
                   braun_replace_min_size o2 =
                     braun_replace_min_size r
                   ==>
                   braun_replace_min_heap le r /\
                   (0 : int) < braun_replace_min_size r)) /\
       !result.
         (case t of
            BraunReplaceMinEmpty => F
          | BraunReplaceMinNode l y r =>
              ?o1.
                (if braun_replace_min_le_root le x l
                 then
                   o1 =
                     (if braun_replace_min_le_root le x r
                      then T
                      else F)
                 else o1 = F) /\
                (if o1 = T
                 then result = BraunReplaceMinNode l x r
                 else
                   let lx = minimum l
                   in
                     if braun_replace_min_le_root le lx r
                     then
                       ?o2.
                         (braun_replace_min_heap le o2 /\
                          braun_replace_min_inv o2 /\
                          (if x = minimum l
                           then
                             braun_replace_min_occ x o2 =
                               braun_replace_min_occ x l
                           else
                             braun_replace_min_occ x o2 =
                               braun_replace_min_occ x l + (1 : int) /\
                             braun_replace_min_occ (minimum l) o2 =
                               braun_replace_min_occ (minimum l) l -
                                 (1 : int)) /\
                          (!e.
                             ~(e = x) ==>
                             ~(e = minimum l) ==>
                             braun_replace_min_occ e o2 =
                               braun_replace_min_occ e l) /\
                          braun_replace_min_size o2 =
                            braun_replace_min_size l) /\
                         result = BraunReplaceMinNode o2 lx r
                     else
                       ?o2.
                         (braun_replace_min_heap le o2 /\
                          braun_replace_min_inv o2 /\
                          (if x = minimum r
                           then
                             braun_replace_min_occ x o2 =
                               braun_replace_min_occ x r
                           else
                             braun_replace_min_occ x o2 =
                               braun_replace_min_occ x r + (1 : int) /\
                             braun_replace_min_occ (minimum r) o2 =
                               braun_replace_min_occ (minimum r) r -
                                 (1 : int)) /\
                          (!e.
                             ~(e = x) ==>
                             ~(e = minimum r) ==>
                             braun_replace_min_occ e o2 =
                               braun_replace_min_occ e r) /\
                          braun_replace_min_size o2 =
                            braun_replace_min_size r) /\
                         result =
                           BraunReplaceMinNode l (minimum r) o2))
         ==>
         braun_replace_min_heap le result /\
         braun_replace_min_inv result /\
         (if x = minimum t
          then
            braun_replace_min_occ x result =
              braun_replace_min_occ x t
          else
            braun_replace_min_occ x result =
              braun_replace_min_occ x t + (1 : int) /\
            braun_replace_min_occ (minimum t) result =
              braun_replace_min_occ (minimum t) t - (1 : int)) /\
         (!e.
            ~(e = x) ==>
            ~(e = minimum t) ==>
            braun_replace_min_occ e result =
              braun_replace_min_occ e t) /\
         braun_replace_min_size result =
           braun_replace_min_size t)``;

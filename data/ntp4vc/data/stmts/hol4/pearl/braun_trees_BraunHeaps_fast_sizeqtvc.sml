(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/braun_trees_BraunHeaps_fast_sizeqtvc: a Braun-tree fast-size
  verification condition relating the recursive balance invariant, subtree
  size bounds, and the computed integer size. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  braun_fast_size_tree =
    BraunFastSizeEmpty
  | BraunFastSizeNode braun_fast_size_tree 'elt braun_fast_size_tree
End

val braun_fast_size_size_def = Define `
  (braun_fast_size_size
      (BraunFastSizeEmpty : 'elt braun_fast_size_tree) = (0 : int)) /\
  (braun_fast_size_size (BraunFastSizeNode l x r) =
     (1 : int) + braun_fast_size_size l + braun_fast_size_size r)`;

val braun_fast_size_inv_def = Define `
  (braun_fast_size_inv
      (BraunFastSizeEmpty : 'elt braun_fast_size_tree) = T) /\
  (braun_fast_size_inv (BraunFastSizeNode l x r) =
     ((braun_fast_size_size l = braun_fast_size_size r \/
       braun_fast_size_size l =
         braun_fast_size_size r + (1 : int)) /\
      braun_fast_size_inv l /\
      braun_fast_size_inv r))`;

val braun_trees_BraunHeaps_fast_size_vc =
  ``!(t : 'elt braun_fast_size_tree).
      braun_fast_size_inv t ==>
      ((case t of
          BraunFastSizeEmpty => T
        | BraunFastSizeNode l x r =>
            ((case t of
                BraunFastSizeEmpty => F
              | BraunFastSizeNode f y f1 => f = r \/ f1 = r) /\
             braun_fast_size_inv r) /\
            (let m = braun_fast_size_size r
             in
               braun_fast_size_inv l /\
               (0 : int) <= m /\
               m <= braun_fast_size_size l /\
               braun_fast_size_size l <= m + (1 : int))) /\
       !result.
         (case t of
            BraunFastSizeEmpty => result = (0 : int)
          | BraunFastSizeNode l x r =>
              let m = braun_fast_size_size r
              in
                ?o1.
                  braun_fast_size_size l = m + o1 /\
                  result = (1 : int) + (2 : int) * m + o1)
         ==>
         result = braun_fast_size_size t)``;

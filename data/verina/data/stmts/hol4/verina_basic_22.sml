(*
  Statement-only formalization of VERINA corpus artifact verina_basic_22,
  catalog title "dissimilarElements": the executable set-accumulation and
  sorting program returns the sorted, duplicate-free symmetric difference of
  two integer arrays and satisfies the source postcondition. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val dissimilarElements_inArray_def = new_definition (
  "dissimilarElements_inArray_def",
  ``dissimilarElements_inArray
      (a : int list) (x : int) =
      MEM x a``
);

val dissimilarElements_precond_def = new_definition (
  "dissimilarElements_precond_def",
  ``dissimilarElements_precond
      (a : int list) (b : int list) <=>
      T``
);

val dissimilarElements_setInsert_def = new_definition (
  "dissimilarElements_setInsert_def",
  ``dissimilarElements_setInsert
      (x : int) (acc : int list) =
      if MEM x acc then acc else x::acc``
);

val dissimilarElements_collect_def = Define `
  (dissimilarElements_collect
      ([] : int list)
      (other : int list)
      (acc : int list) =
     acc) /\
  (dissimilarElements_collect
      (x::xs)
      other
      acc =
     dissimilarElements_collect
       xs
       other
       (if ~dissimilarElements_inArray other x then
          dissimilarElements_setInsert x acc
        else
          acc))
`;

val dissimilarElements_sortInsert_def = Define `
  (dissimilarElements_sortInsert
      (x : int) ([] : int list) =
     [x]) /\
  (dissimilarElements_sortInsert
      x (y::ys) =
     if x <= y then
       x::y::ys
     else
       y::dissimilarElements_sortInsert x ys)
`;

val dissimilarElements_sort_def = Define `
  (dissimilarElements_sort
      ([] : int list) =
     ([] : int list)) /\
  (dissimilarElements_sort
      (x::xs) =
     dissimilarElements_sortInsert
       x (dissimilarElements_sort xs))
`;

val dissimilarElements_def = new_definition (
  "dissimilarElements_def",
  ``dissimilarElements
      (a : int list) (b : int list) =
      let fromA =
        dissimilarElements_collect a b []
      in
      let fromBoth =
        dissimilarElements_collect b a fromA
      in
        dissimilarElements_sort fromBoth``
);

val dissimilarElements_pairwiseLe_def = Define `
  (dissimilarElements_pairwiseLe
      ([] : int list) <=>
     T) /\
  (dissimilarElements_pairwiseLe
      (x::xs) <=>
     EVERY (\y : int. x <= y) xs /\
     dissimilarElements_pairwiseLe xs)
`;

val dissimilarElements_postcond_def = new_definition (
  "dissimilarElements_postcond_def",
  ``dissimilarElements_postcond
      (a : int list)
      (b : int list)
      (result : int list) <=>
      EVERY
        (\x : int.
           dissimilarElements_inArray a x <>
           dissimilarElements_inArray b x)
        result /\
      dissimilarElements_pairwiseLe result /\
      ALL_DISTINCT result /\
      EVERY
        (\x : int.
           if MEM x b then
             ~MEM x result
           else
             MEM x result)
        a /\
      EVERY
        (\x : int.
           if MEM x a then
             ~MEM x result
           else
             MEM x result)
        b``
);

val dissimilarElements_spec_satisfied =
  ``!(a : int list) (b : int list).
      dissimilarElements_precond a b ==>
      dissimilarElements_postcond
        a b (dissimilarElements a b)``;

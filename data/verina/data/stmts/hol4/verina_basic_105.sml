(*
  Statement-only formalization of VERINA corpus artifact verina_basic_105,
  catalog title "arrayProduct": the executable bounded array loop returns the
  element-wise integer product of equal-length arrays, using zero for missing
  reads. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val arrayProduct_precond_def = new_definition (
  "arrayProduct_precond_def",
  ``arrayProduct_precond
      (a : int list) (b : int list) <=>
      LENGTH a = LENGTH b``
);

val arrayProduct_nthD_def = Define `
  (arrayProduct_nthD
      (index : num) ([] : int list) = (0 : int)) /\
  (arrayProduct_nthD
      0 (x::xs) = x) /\
  (arrayProduct_nthD
      (SUC index) (x::xs) =
     arrayProduct_nthD index xs)
`;

val arrayProduct_loopFuel_def = Define `
  (arrayProduct_loopFuel
      (a : int list)
      (b : int list)
      (len : num)
      (i : num)
      (c : int list)
      0 =
     c) /\
  (arrayProduct_loopFuel
      a b len i c (SUC fuel) =
     if i < len then
       let a_val =
         if i < LENGTH a then arrayProduct_nthD i a else (0 : int)
       in
       let b_val =
         if i < LENGTH b then arrayProduct_nthD i b else (0 : int)
       in
       let new_c = LUPDATE (a_val * b_val) i c in
         arrayProduct_loopFuel
           a b len (i + 1) new_c fuel
     else
       c)
`;

val arrayProduct_loop_def = new_definition (
  "arrayProduct_loop_def",
  ``arrayProduct_loop
      (a : int list)
      (b : int list)
      (len : num)
      (i : num)
      (c : int list) =
      arrayProduct_loopFuel a b len i c (len - i)``
);

val arrayProduct_def = new_definition (
  "arrayProduct_def",
  ``arrayProduct (a : int list) (b : int list) =
      let len = LENGTH a in
      let c = REPLICATE len (0 : int) in
        arrayProduct_loop a b len 0 c``
);

val arrayProduct_postcond_def = new_definition (
  "arrayProduct_postcond_def",
  ``arrayProduct_postcond
      (a : int list)
      (b : int list)
      (result : int list) <=>
      LENGTH result = LENGTH a /\
      (!i.
         i < LENGTH a ==>
         arrayProduct_nthD i a * arrayProduct_nthD i b =
         arrayProduct_nthD i result)``
);

val arrayProduct_spec_satisfied =
  ``!(a : int list) (b : int list).
      arrayProduct_precond a b ==>
      arrayProduct_postcond a b (arrayProduct a b)``;

(*
  Statement-only formalization of VERINA corpus artifact verina_basic_106,
  catalog title "arraySum": the executable guarded array loop returns the
  element-wise integer sum of equal-length arrays under its size and pointwise
  correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val arraySum_precond_def = new_definition (
  "arraySum_precond_def",
  ``arraySum_precond
      (a : int list) (b : int list) <=>
      LENGTH a = LENGTH b``
);

val arraySum_nthD_def = Define `
  (arraySum_nthD
      (index : num) ([] : int list) = (0 : int)) /\
  (arraySum_nthD
      0 (x::xs) = x) /\
  (arraySum_nthD
      (SUC index) (x::xs) =
     arraySum_nthD index xs)
`;

val arraySum_loopFuel_def = Define `
  (arraySum_loopFuel
      (a : int list)
      (b : int list)
      (len : num)
      (i : num)
      (c : int list)
      0 =
     c) /\
  (arraySum_loopFuel
      a b len i c (SUC fuel) =
     if i < len then
       let new_c =
         LUPDATE
           (arraySum_nthD i a + arraySum_nthD i b)
           i
           c
       in
         arraySum_loopFuel
           a b len (i + 1) new_c fuel
     else
       c)
`;

val arraySum_loop_def = new_definition (
  "arraySum_loop_def",
  ``arraySum_loop
      (a : int list)
      (b : int list)
      (len : num)
      (i : num)
      (c : int list) =
      arraySum_loopFuel a b len i c (len - i)``
);

val arraySum_def = new_definition (
  "arraySum_def",
  ``arraySum (a : int list) (b : int list) =
      if LENGTH a <> LENGTH b then
        ([] : int list)
      else
        let len = LENGTH a in
        let c = REPLICATE len (0 : int) in
          arraySum_loop a b len 0 c``
);

val arraySum_postcond_def = new_definition (
  "arraySum_postcond_def",
  ``arraySum_postcond
      (a : int list)
      (b : int list)
      (result : int list) <=>
      LENGTH result = LENGTH a /\
      (!i.
         i < LENGTH a ==>
         arraySum_nthD i a + arraySum_nthD i b =
         arraySum_nthD i result)``
);

val arraySum_spec_satisfied =
  ``!(a : int list) (b : int list).
      arraySum_precond a b ==>
      arraySum_postcond a b (arraySum a b)``;

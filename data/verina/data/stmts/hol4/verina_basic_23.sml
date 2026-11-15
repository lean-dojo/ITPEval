(*
  Statement-only formalization of VERINA corpus artifact verina_basic_23,
  catalog title "differenceMinMax": the executable indexed scan of a nonempty
  integer array returns its maximum value minus its minimum value and satisfies
  the corresponding fold-based correctness contract. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val differenceMinMax_precond_def = new_definition (
  "differenceMinMax_precond_def",
  ``differenceMinMax_precond (a : int list) <=>
      LENGTH a > 0``
);

val differenceMinMax_nthD_def = Define `
  (differenceMinMax_nthD
      (index : num) ([] : int list) = (0 : int)) /\
  (differenceMinMax_nthD
      0 (x::xs) = x) /\
  (differenceMinMax_nthD
      (SUC index) (x::xs) =
     differenceMinMax_nthD index xs)
`;

val differenceMinMax_loopFuel_def = Define `
  (differenceMinMax_loopFuel
      (a : int list)
      (i : num)
      (minVal : int)
      (maxVal : int)
      0 =
     maxVal - minVal) /\
  (differenceMinMax_loopFuel
      a i minVal maxVal (SUC fuel) =
     if i < LENGTH a then
       let x = differenceMinMax_nthD i a in
       let newMin = if x < minVal then x else minVal in
       let newMax = if x > maxVal then x else maxVal in
         differenceMinMax_loopFuel
           a (i + 1) newMin newMax fuel
     else
       maxVal - minVal)
`;

val differenceMinMax_loop_def = new_definition (
  "differenceMinMax_loop_def",
  ``differenceMinMax_loop
      (a : int list)
      (i : num)
      (minVal : int)
      (maxVal : int) =
      differenceMinMax_loopFuel
        a i minVal maxVal (LENGTH a - i + 1)``
);

val differenceMinMax_def = new_definition (
  "differenceMinMax_def",
  ``differenceMinMax (a : int list) =
      let first = differenceMinMax_nthD 0 a in
        differenceMinMax_loop a 1 first first``
);

val differenceMinMax_postcond_def = new_definition (
  "differenceMinMax_postcond_def",
  ``differenceMinMax_postcond
      (a : int list) (result : int) <=>
      result +
        FOLDL
          (\acc : int. \x : int.
             if x < acc then x else acc)
          (differenceMinMax_nthD 0 a)
          a =
      FOLDL
        (\acc : int. \x : int.
           if x > acc then x else acc)
        (differenceMinMax_nthD 0 a)
        a``
);

val differenceMinMax_spec_satisfied =
  ``!a : int list.
      differenceMinMax_precond a ==>
      differenceMinMax_postcond a (differenceMinMax a)``;

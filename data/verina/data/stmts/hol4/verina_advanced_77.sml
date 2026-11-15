(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_77,
  catalog title "trapRainWater": the executable two-pointer program computes
  the total water trapped by a natural-number elevation map according to the
  per-position left- and right-maximum specification. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val trapRainWater_nthD_def = Define `
  (trapRainWater_nthD
      (index : num) ([] : num list) = 0) /\
  (trapRainWater_nthD
      0 (x::xs) = x) /\
  (trapRainWater_nthD
      (SUC index) (x::xs) =
     trapRainWater_nthD index xs)
`;

val trapRainWater_max_def = new_definition (
  "trapRainWater_max_def",
  ``trapRainWater_max (a : num) (b : num) =
      if a < b then b else a``
);

val trapRainWater_min_def = new_definition (
  "trapRainWater_min_def",
  ``trapRainWater_min (a : num) (b : num) =
      if a < b then a else b``
);

val trapRainWater_precond_def = new_definition (
  "trapRainWater_precond_def",
  ``trapRainWater_precond (height : num list) <=> T``
);

val trapLoopFuel_def = Define `
  (trapLoopFuel
      (height : num list) 0
      (left : num) (right : num)
      (leftMax : num) (rightMax : num) (water : num) =
     water) /\
  (trapLoopFuel
      height (SUC fuel) left right leftMax rightMax water =
     if left < right then
       let hLeft = trapRainWater_nthD left height in
       let hRight = trapRainWater_nthD right height in
         if hLeft < hRight then
           if leftMax <= hLeft then
             trapLoopFuel
               height fuel (left + 1) right
               hLeft rightMax water
           else
             trapLoopFuel
               height fuel (left + 1) right
               leftMax rightMax (water + (leftMax - hLeft))
         else
           if rightMax <= hRight then
             trapLoopFuel
               height fuel left (right - 1)
               leftMax hRight water
           else
             trapLoopFuel
               height fuel left (right - 1)
               leftMax rightMax (water + (rightMax - hRight))
     else
       water)
`;

val trapLoop_def = new_definition (
  "trapLoop_def",
  ``trapLoop
      (height : num list)
      (left : num) (right : num)
      (leftMax : num) (rightMax : num) (water : num) =
      trapLoopFuel
        height (right - left) left right leftMax rightMax water``
);

val trapRainWater_def = new_definition (
  "trapRainWater_def",
  ``trapRainWater (height : num list) =
      trapLoop height 0 (LENGTH height - 1) 0 0 0``
);

val trapRainWater_waterAt_def = new_definition (
  "trapRainWater_waterAt_def",
  ``trapRainWater_waterAt (height : num list) =
      GENLIST
        (\i : num.
           trapRainWater_min
             (FOLDL trapRainWater_max 0 (TAKE (i + 1) height))
             (FOLDL trapRainWater_max 0 (DROP i height)) -
           trapRainWater_nthD i height)
        (LENGTH height)``
);

val trapRainWater_sum_def = new_definition (
  "trapRainWater_sum_def",
  ``trapRainWater_sum (xs : num list) =
      FOLDL (\acc : num. \x : num. acc + x) 0 xs``
);

val trapRainWater_postcond_def = new_definition (
  "trapRainWater_postcond_def",
  ``trapRainWater_postcond
      (height : num list) (result : num) <=>
      let total =
        trapRainWater_sum (trapRainWater_waterAt height)
      in
        result - total = 0 /\ total <= result``
);

val trapRainWater_spec_satisfied =
  ``!height : num list.
      trapRainWater_precond height ==>
      trapRainWater_postcond
        height (trapRainWater height)``;

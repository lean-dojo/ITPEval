(*
  Statement-only formalization of VERINA artifact verina_advanced_62,
  cataloged as "rain": the executable two-pointer program computes trapped
  rainwater for a nonnegative integer elevation list and satisfies the stated
  prefix/suffix-maximum summation contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val rain_precond_def = new_definition (
  "rain_precond_def",
  ``rain_precond (heights : int list) <=>
      EVERY (\h : int. 0 <= h) heights``
);

val rain_getDefault_def = new_definition (
  "rain_getDefault_def",
  ``rain_getDefault (heights : int list) (index : num) =
      if index < LENGTH heights then EL index heights else (0 : int)``
);

val rain_intMax_def = new_definition (
  "rain_intMax_def",
  ``rain_intMax (x : int) (y : int) =
      if x <= y then y else x``
);

val rain_intMin_def = new_definition (
  "rain_intMin_def",
  ``rain_intMin (x : int) (y : int) =
      if x <= y then x else y``
);

val rain_nonnegativePart_def = new_definition (
  "rain_nonnegativePart_def",
  ``rain_nonnegativePart (x : int) =
      if 0 <= x then x else 0``
);

val rain_aux_def = Define `
  (rain_aux
      0
      (heights : int list)
      (left : num)
      (right : num)
      (leftMax : int)
      (rightMax : int)
      (water : int) =
     water) /\
  (rain_aux
      (SUC fuel)
      heights
      left
      right
      leftMax
      rightMax
      water =
     if right <= left then
       water
     else if
       rain_getDefault heights left <=
       rain_getDefault heights right
     then
       let height = rain_getDefault heights left in
         rain_aux
           fuel
           heights
           (left + 1)
           right
           (rain_intMax leftMax height)
           rightMax
           (water + rain_nonnegativePart (leftMax - height))
     else
       let height = rain_getDefault heights right in
         rain_aux
           fuel
           heights
           left
           (right - 1)
           leftMax
           (rain_intMax rightMax height)
           (water + rain_nonnegativePart (rightMax - height)))
`;

val rain_def = new_definition (
  "rain_def",
  ``rain (heights : int list) =
      if LENGTH heights < 3 then
        (0 : int)
      else
        let n = LENGTH heights in
          rain_aux
            (n - 1)
            heights
            0
            (n - 1)
            (rain_getDefault heights 0)
            (rain_getDefault heights (n - 1))
            0``
);

val rain_leftMaxLoop_def = Define `
  (rain_leftMaxLoop
      0
      (heights : int list)
      (index : num)
      (maximum : int) =
     maximum) /\
  (rain_leftMaxLoop
      (SUC fuel)
      heights
      index
      maximum =
     rain_leftMaxLoop
       fuel
       heights
       (index + 1)
       (rain_intMax maximum (rain_getDefault heights index)))
`;

val rain_maxLeftAt_def = new_definition (
  "rain_maxLeftAt_def",
  ``rain_maxLeftAt (heights : int list) (index : num) =
      rain_leftMaxLoop (index + 1) heights 0 0``
);

val rain_rightMaxLoop_def = Define `
  (rain_rightMaxLoop ([] : int list) (maximum : int) =
     maximum) /\
  (rain_rightMaxLoop (height::remaining) maximum =
     rain_rightMaxLoop
       remaining
       (rain_intMax maximum height))
`;

val rain_maxRightAt_def = new_definition (
  "rain_maxRightAt_def",
  ``rain_maxRightAt (heights : int list) (index : num) =
      rain_rightMaxLoop (DROP index heights) 0``
);

val rain_waterAt_def = new_definition (
  "rain_waterAt_def",
  ``rain_waterAt (heights : int list) (index : num) =
      rain_nonnegativePart
        (rain_intMin
           (rain_maxLeftAt heights index)
           (rain_maxRightAt heights index) -
         rain_getDefault heights index)``
);

val rain_sumWater_def = Define `
  (rain_sumWater
      0
      (heights : int list)
      (index : num)
      (accumulator : int) =
     accumulator) /\
  (rain_sumWater
      (SUC fuel)
      heights
      index
      accumulator =
     rain_sumWater
       fuel
       heights
       (index + 1)
       (accumulator + rain_waterAt heights index))
`;

val rain_postcond_def = new_definition (
  "rain_postcond_def",
  ``rain_postcond (heights : int list) (result : int) <=>
      0 <= result /\
      (if LENGTH heights < 3 then
         result = 0
       else
         result =
           rain_sumWater (LENGTH heights) heights 0 0)``
);

val rain_spec_satisfied =
  ``!heights : int list.
      rain_precond heights ==>
      rain_postcond heights (rain heights)``;

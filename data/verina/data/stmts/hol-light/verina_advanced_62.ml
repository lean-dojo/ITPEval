(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_62,
  catalog title "rain": an executable two-pointer scan computes trapped
  rainwater for a nonnegative integer elevation list, together with the
  independently summed per-index postcondition and total correctness contract.
  This file contains no proof.
*)

let rain_precond = new_definition
  `rain_precond (heights:int list) <=>
     ALL (\height:int. (&0:int) <= height) heights`;;

let rain_int_max = new_definition
  `rain_int_max (a:int) (b:int) =
     if a <= b then b else a`;;

let rain_int_min = new_definition
  `rain_int_min (a:int) (b:int) =
     if a <= b then a else b`;;

let rain_getDefault = new_definition
  `rain_getDefault (heights:int list) (index:num) =
     if index < LENGTH heights then EL index heights else (&0:int)`;;

let rain_aux =
  new_recursive_definition num_RECURSION
    `(!heights:int list. !left:num. !right:num.
      !leftMax:int. !rightMax:int. !water:int.
        rain_aux 0 heights left right leftMax rightMax water = water) /\
     (!fuel:num. !heights:int list. !left:num. !right:num.
      !leftMax:int. !rightMax:int. !water:int.
        rain_aux (SUC fuel) heights left right leftMax rightMax water =
        if right <= left then water
        else if rain_getDefault heights left <=
                rain_getDefault heights right then
          let current = rain_getDefault heights left in
          let newLeftMax = rain_int_max leftMax current in
          let newWater =
            water + rain_int_max (&0:int) (leftMax - current) in
          rain_aux fuel heights (left + 1) right
            newLeftMax rightMax newWater
        else
          let current = rain_getDefault heights right in
          let newRightMax = rain_int_max rightMax current in
          let newWater =
            water + rain_int_max (&0:int) (rightMax - current) in
          rain_aux fuel heights left (right - 1)
            leftMax newRightMax newWater)`;;

let rain = new_definition
  `rain (heights:int list) =
     if LENGTH heights < 3 then (&0:int)
     else
       let n = LENGTH heights in
       rain_aux n heights 0 (n - 1)
         (rain_getDefault heights 0)
         (rain_getDefault heights (n - 1))
         (&0:int)`;;

let rain_maxSteps =
  new_recursive_definition num_RECURSION
    `(!heights:int list. !index:num. !maxSoFar:int.
        rain_maxSteps 0 heights index maxSoFar = maxSoFar) /\
     (!steps:num. !heights:int list. !index:num. !maxSoFar:int.
        rain_maxSteps (SUC steps) heights index maxSoFar =
        rain_maxSteps steps heights (index + 1)
          (rain_int_max maxSoFar
            (rain_getDefault heights index)))`;;

let rain_maxLeftAt = new_definition
  `rain_maxLeftAt (heights:int list) (index:num) =
     rain_maxSteps (index + 1) heights 0 (&0:int)`;;

let rain_maxRightAt = new_definition
  `rain_maxRightAt (heights:int list) (index:num) =
     rain_maxSteps (LENGTH heights - index)
       heights index (&0:int)`;;

let rain_waterAt = new_definition
  `rain_waterAt (heights:int list) (index:num) =
     rain_int_max (&0:int)
       (rain_int_min
          (rain_maxLeftAt heights index)
          (rain_maxRightAt heights index) -
        rain_getDefault heights index)`;;

let rain_sumWater =
  new_recursive_definition num_RECURSION
    `(!heights:int list. !index:num. !acc:int.
        rain_sumWater 0 heights index acc = acc) /\
     (!steps:num. !heights:int list. !index:num. !acc:int.
        rain_sumWater (SUC steps) heights index acc =
        rain_sumWater steps heights (index + 1)
          (acc + rain_waterAt heights index))`;;

let rain_postcond = new_definition
  `rain_postcond (heights:int list) (result:int) <=>
     (&0:int) <= result /\
     (if LENGTH heights < 3 then result = (&0:int)
      else
        result =
          rain_sumWater (LENGTH heights) heights 0 (&0:int))`;;

let rain_spec_satisfied =
  `!heights:int list.
     rain_precond heights
     ==> rain_postcond heights (rain heights)`;;

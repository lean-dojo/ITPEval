(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_77,
  catalog title "trapRainWater": a deterministic two-pointer program computes
  trapped rain water over natural-number elevations, with its total
  precondition and per-index water-sum correctness contract. This file
  contains no proof.
*)

let trapRainWater_precond = new_definition
  `trapRainWater_precond (height:num list) <=> T`;;

let trapRainWater_get =
  new_recursive_definition num_RECURSION
    `(!height:num list.
        trapRainWater_get 0 height =
        if height = [] then 0 else HD height) /\
     (!i:num. !height:num list.
        trapRainWater_get (SUC i) height =
        if height = [] then 0
        else trapRainWater_get i (TL height))`;;

let trapRainWater_loopFuel =
  new_recursive_definition num_RECURSION
    `(!height:num list.
      !left:num. !right:num.
      !leftMax:num. !rightMax:num. !water:num.
        trapRainWater_loopFuel
          0 height left right leftMax rightMax water =
        water) /\
     (!fuel:num. !height:num list.
      !left:num. !right:num.
      !leftMax:num. !rightMax:num. !water:num.
        trapRainWater_loopFuel
          (SUC fuel) height left right leftMax rightMax water =
        if left < right then
          let hLeft = trapRainWater_get left height in
          let hRight = trapRainWater_get right height in
          if hLeft < hRight then
            if hLeft >= leftMax then
              trapRainWater_loopFuel
                fuel height (left + 1) right
                hLeft rightMax water
            else
              trapRainWater_loopFuel
                fuel height (left + 1) right
                leftMax rightMax (water + (leftMax - hLeft))
          else
            if hRight >= rightMax then
              trapRainWater_loopFuel
                fuel height left (right - 1)
                leftMax hRight water
            else
              trapRainWater_loopFuel
                fuel height left (right - 1)
                leftMax rightMax (water + (rightMax - hRight))
        else
          water)`;;

let trapLoop = new_definition
  `trapLoop
      (height:num list)
      (left:num) (right:num)
      (leftMax:num) (rightMax:num) (water:num) =
     trapRainWater_loopFuel
       (right - left) height left right leftMax rightMax water`;;

let trapRainWater = new_definition
  `trapRainWater (height:num list) =
     trapLoop height 0 (LENGTH height - 1) 0 0 0`;;

let trapRainWater_take =
  new_recursive_definition num_RECURSION
    `(!height:num list.
        trapRainWater_take 0 height = []) /\
     (!n:num. !height:num list.
        trapRainWater_take (SUC n) height =
        if height = [] then []
        else CONS (HD height)
          (trapRainWater_take n (TL height)))`;;

let trapRainWater_drop =
  new_recursive_definition num_RECURSION
    `(!height:num list.
        trapRainWater_drop 0 height = height) /\
     (!n:num. !height:num list.
        trapRainWater_drop (SUC n) height =
        if height = [] then []
        else trapRainWater_drop n (TL height))`;;

let trapRainWater_maxFold =
  new_recursive_definition list_RECURSION
    `(!acc:num.
        trapRainWater_maxFold acc [] = acc) /\
     (!x:num. !xs:num list. !acc:num.
        trapRainWater_maxFold acc (CONS x xs) =
        trapRainWater_maxFold (MAX acc x) xs)`;;

let trapRainWater_waterAtFrom =
  new_recursive_definition num_RECURSION
    `(!height:num list. !i:num.
        trapRainWater_waterAtFrom 0 height i = []) /\
     (!count:num. !height:num list. !i:num.
        trapRainWater_waterAtFrom (SUC count) height i =
        let lmax =
          trapRainWater_maxFold 0
            (trapRainWater_take (i + 1) height) in
        let rmax =
          trapRainWater_maxFold 0
            (trapRainWater_drop i height) in
        CONS
          (MIN lmax rmax - trapRainWater_get i height)
          (trapRainWater_waterAtFrom
            count height (i + 1)))`;;

let trapRainWater_waterAt = new_definition
  `trapRainWater_waterAt (height:num list) =
     trapRainWater_waterAtFrom (LENGTH height) height 0`;;

let trapRainWater_sumFold =
  new_recursive_definition list_RECURSION
    `(!acc:num.
        trapRainWater_sumFold acc [] = acc) /\
     (!x:num. !xs:num list. !acc:num.
        trapRainWater_sumFold acc (CONS x xs) =
        trapRainWater_sumFold (acc + x) xs)`;;

let trapRainWater_postcond = new_definition
  `trapRainWater_postcond
      (height:num list) (result:num) <=>
     let total =
       trapRainWater_sumFold 0
         (trapRainWater_waterAt height) in
     result - total = 0 /\ total <= result`;;

let trapRainWater_spec_satisfied =
  `!height:num list.
     trapRainWater_precond height
     ==> trapRainWater_postcond
           height (trapRainWater height)`;;

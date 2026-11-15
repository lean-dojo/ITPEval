(*
  Statement-only formalization of VERINA corpus artifact verina_basic_13,
  catalog title "cubeElements": an executable map replaces every element of
  an integer array with its cube, together with its total precondition and
  length-and-pointwise correctness contract. This file contains no proof.
*)

let cubeElements_precond = new_definition
  `cubeElements_precond (a:int list) <=> T`;;

let cubeElements = new_definition
  `cubeElements (a:int list) =
     MAP (\x:int. x * x * x) a`;;

let cubeElements_postcond = new_definition
  `cubeElements_postcond (a:int list) (result:int list) <=>
     LENGTH result = LENGTH a /\
     (!i:num.
        i < LENGTH a
        ==> EL i result = EL i a * EL i a * EL i a)`;;

let cubeElements_spec_satisfied =
  `!a:int list.
     cubeElements_precond a
     ==> cubeElements_postcond a (cubeElements a)`;;

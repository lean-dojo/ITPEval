(*
  Statement-only formalization of VERINA corpus artifact verina_basic_12,
  catalog title "cubeSurfaceArea": an executable natural-number computation
  returns six times the square of a cube's edge length, together with its total
  precondition and truncated-subtraction correctness contract. This file
  contains no proof.
*)

let cubeSurfaceArea_precond = new_definition
  `cubeSurfaceArea_precond (size:num) <=> T`;;

let cubeSurfaceArea = new_definition
  `cubeSurfaceArea (size:num) = 6 * size * size`;;

let cubeSurfaceArea_postcond = new_definition
  `cubeSurfaceArea_postcond (size:num) (result:num) <=>
     result - 6 * size * size = 0 /\
     6 * size * size - result = 0`;;

let cubeSurfaceArea_spec_satisfied =
  `!size:num.
     cubeSurfaceArea_precond size
     ==> cubeSurfaceArea_postcond size (cubeSurfaceArea size)`;;

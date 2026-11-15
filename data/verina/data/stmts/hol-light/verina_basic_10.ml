(*
  Statement-only formalization of VERINA corpus artifact verina_basic_10,
  catalog title "isGreater": an executable universal scan decides whether an
  integer is strictly greater than every element of a nonempty integer
  sequence, together with its Boolean correctness contract. This file contains
  no proof.
*)

let isGreater_precond = new_definition
  `isGreater_precond (n:int) (a:int list) <=>
     LENGTH a > 0`;;

let isGreater = new_definition
  `isGreater (n:int) (a:int list) =
     ALL (\x:int. n > x) a`;;

let isGreater_postcond = new_definition
  `isGreater_postcond
      (n:int) (a:int list) (result:bool) <=>
     ((!i:num. i < LENGTH a ==> n > EL i a) <=> result)`;;

let isGreater_spec_satisfied =
  `!n:int. !a:int list.
     isGreater_precond n a
     ==> isGreater_postcond n a (isGreater n a)`;;

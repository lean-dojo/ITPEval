(*
  Statement-only formalization of VERINA corpus artifact verina_basic_66
  (verina__hol-light__verina_basic_66), catalog title "ComputeIsEven": an
  executable integer remainder test returns true exactly when the input is
  twice an integer, together with its total precondition and correctness
  contract. This file contains no proof.
*)

let ComputeIsEven_precond = new_definition
  `ComputeIsEven_precond (x:int) <=> T`;;

let ComputeIsEven = new_definition
  `ComputeIsEven (x:int) =
     if x rem (&2:int) = (&0:int) then T else F`;;

let ComputeIsEven_postcond = new_definition
  `ComputeIsEven_postcond (x:int) (result:bool) <=>
     ((result = T) <=> (?k:int. x = (&2:int) * k))`;;

let ComputeIsEven_spec_satisfied =
  `!x:int.
     ComputeIsEven_precond x
     ==> ComputeIsEven_postcond x (ComputeIsEven x)`;;

(*
  Statement-only formalization of VERINA corpus artifact verina_basic_88
  (verina__hol-light__verina_basic_88), catalog title "ToArray": an executable
  conversion of an integer list to an extensionally represented integer array,
  preserving its length and every element at each valid index. This file
  contains no proof.
*)

let ToArray_precond = new_definition
  `ToArray_precond (xs:int list) <=> T`;;

let ToArray = new_definition
  `ToArray (xs:int list) = xs`;;

let ToArray_postcond = new_definition
  `ToArray_postcond (xs:int list) (result:int list) <=>
     LENGTH result = LENGTH xs /\
     (!i:num.
        i < LENGTH xs
        ==> EL i result = EL i xs)`;;

let ToArray_spec_satisfied =
  `!xs:int list.
     ToArray_precond xs
     ==> ToArray_postcond xs (ToArray xs)`;;

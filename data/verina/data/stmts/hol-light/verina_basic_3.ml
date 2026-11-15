(*
  Statement-only formalization of VERINA corpus artifact verina_basic_3,
  catalog title "isDivisibleBy11": an executable integer remainder test
  returns true exactly when the input is divisible by eleven, together with
  its total precondition and two-branch correctness contract. This file
  contains no proof.
*)

let isDivisibleBy11_precond = new_definition
  `isDivisibleBy11_precond (n:int) <=> T`;;

let isDivisibleBy11 = new_definition
  `isDivisibleBy11 (n:int) =
     (n rem (&11:int) = (&0:int))`;;

let isDivisibleBy11_postcond = new_definition
  `isDivisibleBy11_postcond (n:int) (result:bool) <=>
     (result ==> (?k:int. n = (&11:int) * k)) /\
     (~result ==> (!k:int. ~(n = (&11:int) * k)))`;;

let isDivisibleBy11_spec_satisfied =
  `!n:int.
     isDivisibleBy11_precond n
     ==> isDivisibleBy11_postcond n (isDivisibleBy11 n)`;;

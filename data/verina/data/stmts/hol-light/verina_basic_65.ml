(*
  Statement-only formalization of VERINA corpus artifact verina_basic_65
  (verina__hol-light__verina_basic_65), catalog title "SquareRoot": an
  executable bounded natural-number loop computes the integer square root,
  together with its total precondition and exact two-sided square-bound
  correctness contract. This file contains no proof.
*)

let SquareRoot_precond = new_definition
  `SquareRoot_precond (N:num) <=> T`;;

let SquareRoot_boundedLoop =
  new_recursive_definition num_RECURSION
    `(!N:num. !r:num.
        SquareRoot_boundedLoop 0 N r = r) /\
     (!bound:num. !N:num. !r:num.
        SquareRoot_boundedLoop (SUC bound) N r =
        if (r + 1) * (r + 1) <= N then
          SquareRoot_boundedLoop bound N (r + 1)
        else
          r)`;;

let SquareRoot = new_definition
  `SquareRoot (N:num) =
     SquareRoot_boundedLoop (N + 1) N 0`;;

let SquareRoot_postcond = new_definition
  `SquareRoot_postcond (N:num) (result:num) <=>
     result * result <= N /\
     N < (result + 1) * (result + 1)`;;

let SquareRoot_spec_satisfied =
  `!N:num.
     SquareRoot_precond N
     ==> SquareRoot_postcond N (SquareRoot N)`;;

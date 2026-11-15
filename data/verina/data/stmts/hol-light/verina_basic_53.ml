(*
  Statement-only formalization of VERINA corpus artifact verina_basic_53
  (verina__hol-light__verina_basic_53), catalog title "CalSum": an executable
  natural-number recursion computes the sum from 1 through N, together with
  its total precondition and doubled closed-form correctness contract. This
  file contains no proof.
*)

let CalSum_precond = new_definition
  `CalSum_precond (N:num) <=> T`;;

let CalSum_loop =
  new_recursive_definition num_RECURSION
    `(CalSum_loop 0 = 0) /\
     (!n:num.
        CalSum_loop (SUC n) =
        SUC n + CalSum_loop n)`;;

let CalSum = new_definition
  `CalSum (N:num) = CalSum_loop N`;;

let CalSum_postcond = new_definition
  `CalSum_postcond (N:num) (result:num) <=>
     2 * result = N * (N + 1)`;;

let CalSum_spec_satisfied =
  `!N:num.
     CalSum_precond N
     ==> CalSum_postcond N (CalSum N)`;;

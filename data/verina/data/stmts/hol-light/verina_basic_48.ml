(*
  Statement-only formalization of VERINA corpus artifact verina_basic_48
  (verina__hol-light__verina_basic_48), catalog title "isPerfectSquare": an
  executable fuel-bounded natural-number search decides whether its input is
  a perfect square, together with its total precondition and exact Boolean
  correctness contract. This file contains no proof.
*)

let isPerfectSquare_precond = new_definition
  `isPerfectSquare_precond (n:num) <=> T`;;

let isPerfectSquare_check =
  new_recursive_definition num_RECURSION
    `(!n:num. !x:num.
        isPerfectSquare_check 0 n x = F) /\
     (!fuel:num. !n:num. !x:num.
        isPerfectSquare_check (SUC fuel) n x =
        if x * x > n then
          F
        else if x * x = n then
          T
        else
          isPerfectSquare_check fuel n (x + 1))`;;

let isPerfectSquare = new_definition
  `isPerfectSquare (n:num) =
     if n = 0 then
       T
     else
       isPerfectSquare_check n n 1`;;

let isPerfectSquare_postcond = new_definition
  `isPerfectSquare_postcond (n:num) (result:bool) <=>
     (result <=> ?i:num. i * i = n)`;;

let isPerfectSquare_spec_satisfied =
  `!n:num.
     isPerfectSquare_precond n
     ==> isPerfectSquare_postcond n (isPerfectSquare n)`;;

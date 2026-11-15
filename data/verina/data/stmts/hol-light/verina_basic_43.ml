(*
  Statement-only formalization of VERINA corpus artifact verina_basic_43
  (verina__hol-light__verina_basic_43), catalog title
  "sumOfFourthPowerOfOddNumbers": an executable natural-number recursion sums
  the fourth powers of the first n odd numbers, together with its total
  precondition and polynomial correctness contract. This file contains no
  proof.
*)

let sumOfFourthPowerOfOddNumbers_precond = new_definition
  `sumOfFourthPowerOfOddNumbers_precond (n:num) <=> T`;;

let sumOfFourthPowerOfOddNumbers =
  new_recursive_definition num_RECURSION
    `(sumOfFourthPowerOfOddNumbers 0 = 0) /\
     (!n:num.
        sumOfFourthPowerOfOddNumbers (SUC n) =
        sumOfFourthPowerOfOddNumbers n + (2 * n + 1) EXP 4)`;;

let sumOfFourthPowerOfOddNumbers_postcond = new_definition
  `sumOfFourthPowerOfOddNumbers_postcond
      (n:num) (result:num) <=>
     15 * result =
     n * (2 * n + 1) *
       (((7 + 24 * n EXP 3) - 12 * n EXP 2) - 14 * n)`;;

let sumOfFourthPowerOfOddNumbers_spec_satisfied =
  `!n:num.
     sumOfFourthPowerOfOddNumbers_precond n
     ==> sumOfFourthPowerOfOddNumbers_postcond
           n (sumOfFourthPowerOfOddNumbers n)`;;

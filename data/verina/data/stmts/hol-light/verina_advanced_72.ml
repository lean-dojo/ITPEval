(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_72,
  catalog title "singleDigitPrimeFactor": an executable natural-number
  computation returns the smallest prime factor among 2, 3, 5, and 7, or zero
  when none applies, together with its total precondition and correctness
  contract. This file contains no proof.
*)

let singleDigitPrimeFactor_precond = new_definition
  `singleDigitPrimeFactor_precond (n:num) <=> T`;;

let singleDigitPrimeFactor = new_definition
  `singleDigitPrimeFactor (n:num) =
     if n = 0 then 0
     else if n MOD 2 = 0 then 2
     else if n MOD 3 = 0 then 3
     else if n MOD 5 = 0 then 5
     else if n MOD 7 = 0 then 7
     else 0`;;

let singleDigitPrimeFactor_range =
  new_recursive_definition num_RECURSION
    `(singleDigitPrimeFactor_range 0 = []) /\
     (!n:num.
        singleDigitPrimeFactor_range (SUC n) =
        APPEND (singleDigitPrimeFactor_range n) (CONS n []))`;;

let singleDigitPrimeFactor_postcond = new_definition
  `singleDigitPrimeFactor_postcond
      (n:num) (result:num) <=>
     MEM result [0; 2; 3; 5; 7] /\
     (result = 0
      ==> (n = 0 \/
           ALL (\p:num. ~(n MOD p = 0)) [2; 3; 5; 7])) /\
     (~(result = 0)
      ==> ~(n = 0) /\
          n MOD result = 0 /\
          ALL
            (\p:num.
               MEM p [2; 3; 5; 7]
               ==> ~(n MOD p = 0))
            (singleDigitPrimeFactor_range result))`;;

let singleDigitPrimeFactor_spec_satisfied =
  `!n:num.
     singleDigitPrimeFactor_precond n
     ==> singleDigitPrimeFactor_postcond
           n (singleDigitPrimeFactor n)`;;

(*
  Statement-only formalization of VERINA corpus artifact verina_basic_28
  (verina__hol-light__verina_basic_28), catalog title "isPrime": a
  deterministic fuel-bounded divisor scan decides primality for natural
  numbers at least two and is connected to its exact Boolean divisibility
  correctness contract. This file contains no proof.
*)

let isPrime_precond = new_definition
  `isPrime_precond (n:num) <=>
     2 <= n`;;

let isPrime_check =
  new_recursive_definition num_RECURSION
    `(!n:num. !i:num.
        isPrime_check 0 n i = T) /\
     (!fuel:num. !n:num. !i:num.
        isPrime_check (SUC fuel) n i =
        if i * i > n then
          T
        else if n MOD i = 0 then
          F
        else
          isPrime_check fuel n (i + 1))`;;

let isPrime = new_definition
  `isPrime (n:num) =
     isPrime_check n n 2`;;

let isPrime_rangeFrom =
  new_recursive_definition num_RECURSION
    `(!start:num.
        isPrime_rangeFrom 0 start = []) /\
     (!count:num. !start:num.
        isPrime_rangeFrom (SUC count) start =
        CONS start
          (isPrime_rangeFrom count (start + 1)))`;;

let isPrime_candidates = new_definition
  `isPrime_candidates (n:num) =
     isPrime_rangeFrom (n - 2) 2`;;

let isPrime_postcond = new_definition
  `isPrime_postcond (n:num) (result:bool) <=>
     (result
      ==> ALL
            (\k:num. ~(n MOD k = 0))
            (isPrime_candidates n)) /\
     (~result
      ==> EX
            (\k:num. n MOD k = 0)
            (isPrime_candidates n))`;;

let isPrime_spec_satisfied =
  `!n:num.
     isPrime_precond n
     ==> isPrime_postcond n (isPrime n)`;;

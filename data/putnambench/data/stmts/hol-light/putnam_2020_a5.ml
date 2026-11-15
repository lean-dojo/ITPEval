(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2020_a5
  (putnambench__hol-light__putnam_2020_a5): the greatest integer having
  exactly 2020 representations as a sum of distinct positive-index Fibonacci
  numbers. This file contains no proof.
*)

let statement =
  `!fib:num->num.
     fib 0 = 0 /\
     fib 1 = 1 /\
     (!k:num. fib (k + 2) = fib (k + 1) + fib k)
     ==>
     let representations =
       \n:int.
         {S:num->bool |
            FINITE S /\
            (!k:num. k IN S ==> 0 < k) /\
            (&(nsum S fib):int) = n} in
     let a = \n:int. CARD (representations n) in
     let solution = (&(fib 4040):int) - &1 in
     a solution = 2020 /\
     (!n:int. a n = 2020 ==> n <= solution)`;;

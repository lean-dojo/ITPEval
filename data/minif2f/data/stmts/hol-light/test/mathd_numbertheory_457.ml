(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_457:
  a positive natural number whose factorial is divisible by 80325 is at least
  17. This file contains no proof.
*)

let statement =
  `!n:num.
     0 < n /\
     80325 divides (FACT n)
     ==> 17 <= n`;;

(*
  Statement-only formalization of Thousand Theorems corpus artifact Q670235,
  "Fundamental theorem of arithmetic": every list of prime natural numbers
  with product n is a permutation of the canonical nondecreasing prime-factor
  list of n. This file contains no proof.
*)

needs "Library/prime.ml";;
needs "Permutation/permuted.ml";;

let q670235_prime_factors_list = new_definition
  `q670235_prime_factors_list n =
     if n = 0 then []
     else @ps:num list.
       ITLIST (*) ps 1 = n /\
       ALL prime ps /\
       PAIRWISE (\p q. p <= q) ps`;;

let Q670235_FUNDAMENTAL_THEOREM_OF_ARITHMETIC =
  `!n (l:num list).
     ITLIST (*) l 1 = n /\
     ALL prime l
     ==> l PERMUTED q670235_prime_factors_list n`;;

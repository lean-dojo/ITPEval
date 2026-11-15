(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_b5
  (putnambench__hol-light__putnam_2023_b5): classification of the positive
  integers admitting square-root permutations for multiplication modulo n.
  This file contains no proof.
*)

needs "Library/permutations.ml";;

let statement =
  `!n:num.
     (0 < n /\
      (!m:int.
         coprime(m,&n)
         ==> ?p:num->num.
               p permutes (1..n) /\
               (!k:num.
                  k IN 1..n
                  ==> ((&(p (p k)):int) == m * &k) (mod &n))))
     <=>
     n = 1 \/ n MOD 4 = 2`;;

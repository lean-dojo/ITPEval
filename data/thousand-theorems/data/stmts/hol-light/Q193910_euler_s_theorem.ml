(*
  Statement-only formalization of Thousand Theorems corpus artifact Q193910,
  "Euler's theorem": for all natural numbers x and n, if x and n are coprime,
  then x raised to Euler's totient of n is congruent to 1 modulo n. This file
  contains no proof.
*)

needs "Library/pocklington.ml";;

prioritize_num();;

let Q193910_EULERS_THEOREM =
  `!x n:num. coprime(x,n) ==> (x EXP (phi n) == 1) (mod n)`;;

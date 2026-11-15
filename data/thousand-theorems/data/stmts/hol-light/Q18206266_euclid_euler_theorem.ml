(*
  Statement-only formalization of Thousand Theorems corpus artifact Q18206266,
  "Euclid–Euler theorem": every even perfect natural number is a power of two
  times a Mersenne prime of the form 2^(k + 1) - 1. This file contains no proof.
*)

let Q18206266_EUCLID_EULER_THEOREM =
  `let perfect =
     \n:num.
       nsum {d:num | d divides n /\ d < n} (\d. d) = n /\ 0 < n in
   !n:num.
     EVEN n /\ perfect n
     ==> ?k:num.
           prime (2 EXP (k + 1) - 1) /\
           n = 2 EXP k * (2 EXP (k + 1) - 1)`;;

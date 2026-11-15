(*
  Statement-only formalization of miniF2F test artifact aime_1991_p9: under
  the given trigonometric constraints, the reduced rational value of
  1 / sin x + 1 / tan x has numerator plus denominator 44. This file
  contains no proof.
*)

let statement =
  `!x:real p:int q:int.
     &0 < q /\
     gcd (p,q) = &1 /\
     (&1 / cos x + tan x = &22 / &7) /\
     (&1 / sin x + &1 / tan x =
      real_of_int p / real_of_int q)
     ==> p + q = &44`;;

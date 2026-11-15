(*
  Statement-only formalization of miniF2F test problem amc12a_2020_p25. This file contains no
  proof.
*)

needs "Library/floor.ml";;

let statement =
  `!p q:num S:real->bool.
     0 < q /\
     gcd (p,q) = 1 /\
     FINITE S /\
     (!x. x IN S <=>
          floor x * (x - floor x) = (&p / &q) * x pow 2) /\
     sum S (\k. k) = &420
     ==> p + q = 929`;;

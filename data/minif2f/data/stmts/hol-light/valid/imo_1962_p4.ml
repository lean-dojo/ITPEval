(*
  Statement-only formalization of miniF2F valid problem imo_1962_p4,
  classifying the real solutions of
  cos(x)^2 + cos(2x)^2 + cos(3x)^2 = 1 into three integer-indexed
  trigonometric families. This file contains no proof.
*)

needs "Library/transc.ml";;

let imo_1962_p4 =
  `!x:real.
     (cos x) pow 2 + (cos (&2 * x)) pow 2 + (cos (&3 * x)) pow 2 = &1
     ==> (?m:int. x = pi / &2 + real_of_int m * pi) \/
         (?m:int. x = pi / &4 + real_of_int m * pi / &2) \/
         (?m:int. x = pi / &6 + real_of_int m * pi / &3)`;;

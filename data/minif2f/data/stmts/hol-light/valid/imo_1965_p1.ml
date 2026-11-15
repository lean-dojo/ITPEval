(*
  Statement-only formalization of miniF2F valid artifact imo_1965_p1:
  a real angle in [0, 2*pi] satisfying two inequalities involving sine,
  cosine, absolute value, and square roots lies in [pi/4, 7*pi/4].
  This file contains no proof.
*)

needs "Library/transc.ml";;

let imo_1965_p1 =
  `!x:real.
     &0 <= x /\
     x <= &2 * pi /\
     &2 * cos x <=
       abs (sqrt (&1 + sin (&2 * x)) - sqrt (&1 - sin (&2 * x))) /\
     abs (sqrt (&1 + sin (&2 * x)) - sqrt (&1 - sin (&2 * x))) <= sqrt (&2)
     ==> pi / &4 <= x /\ x <= &7 * pi / &4`;;

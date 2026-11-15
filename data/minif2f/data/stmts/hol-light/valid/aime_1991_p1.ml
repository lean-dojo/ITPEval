(*
  Statement-only formalization of miniF2F valid problem aime_1991_p1. This file contains no
  proof.
*)

let statement = `!x:num y:num.
    (0 < x /\ 0 < y) /\
    (x * y + (x + y) = 71) /\
    ((x EXP 2) * y + x * (y EXP 2) = 880)
    ==> x EXP 2 + y EXP 2 = 146`;;

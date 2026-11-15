(*
  Statement-only formalization of miniF2F test problem imo_1997_p5, classifying the
  positive natural-number solutions of x^(y^2) = y^x. This file contains no proof.
*)

let statement =
  `!x y:num.
     0 < x /\ 0 < y /\ x EXP (y EXP 2) = y EXP x
     ==> (x,y) = (1,1) \/ (x,y) = (16,2) \/ (x,y) = (27,3)`;;

(*
  Statement-only formalization of miniF2F test problem aime_1987_p5. This file contains no
  proof.
*)

let statement = `!x y:int.
  y pow 2 + &3 * (x pow 2 * y pow 2) = &30 * x pow 2 + &517
  ==> &3 * (x pow 2 * y pow 2) = &588`;;

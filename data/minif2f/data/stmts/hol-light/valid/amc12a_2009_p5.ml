(*
  Statement-only formalization of miniF2F valid problem amc12a_2009_p5. This file contains no
  proof.
*)

let statement =
  `!x:real.
    x pow 3 - (x + &1) * (x - &1) * x = &5
    ==> x pow 3 = &125`;;

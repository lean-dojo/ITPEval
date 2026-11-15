(*
  Statement-only formalization of miniF2F valid problem amc12a_2011_p18. This file contains no
  proof.
*)

let statement =
  `!x y:real.
    abs (x + y) + abs (x - y) = &2
    ==> x pow 2 - &6 * x + y pow 2 <= &8`;;

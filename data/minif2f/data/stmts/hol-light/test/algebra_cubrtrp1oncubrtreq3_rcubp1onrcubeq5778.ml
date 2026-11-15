(*
  Statement-only formalization of miniF2F test problem
  algebra_cubrtrp1oncubrtreq3_rcubp1onrcubeq5778. This file contains no proof.
*)

let statement =
  `!r:real.
     (?x:real. x pow 3 = r /\ x + &1 / x = &3)
     ==> r pow 3 + &1 / (r pow 3) = &5778`;;

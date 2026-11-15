(*
  Statement-only formalization of miniF2F test problem
  algebra_apbon2pownleqapownpbpowon2: the power inequality comparing the
  midpoint of two positive reals with the average of their positive natural
  powers. This file contains no proof.
*)

let statement =
  `!a b:real. !n:num.
     (&0 < a /\ &0 < b) /\
     0 < n
     ==> ((a + b) / &2) pow n <= (a pow n + b pow n) / &2`;;

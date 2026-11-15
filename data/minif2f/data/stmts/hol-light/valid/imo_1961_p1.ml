(*
  Statement-only formalization of miniF2F valid problem imo_1961_p1. This file contains no
  proof.
*)

(*
  miniF2F imo_1961_p1: for positive pairwise-distinct real numbers x, y, and z
  satisfying x * y = z^2, their sum a and sum of squares b^2 obey
  0 < a, b^2 < a^2, and a^2 < 3 * b^2.
  This is a statement-only formalization and contains no proof.
*)

let imo_1961_p1 =
  `!x y z a b:real.
     &0 < x /\
     &0 < y /\
     &0 < z /\
     ~(x = y) /\
     ~(y = z) /\
     ~(z = x) /\
     x + y + z = a /\
     x pow 2 + y pow 2 + z pow 2 = b pow 2 /\
     x * y = z pow 2
     ==> &0 < a /\
         b pow 2 < a pow 2 /\
         a pow 2 < &3 * b pow 2`;;

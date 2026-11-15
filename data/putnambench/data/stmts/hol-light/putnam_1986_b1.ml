(*
  Statement-only formalization of PutnamBench artifact putnam_1986_b1:
  the stated equal-area conditions for a rectangle and an isosceles triangle
  inscribed in a unit circle force the rectangle height to be 2/5.
  This file contains no proof.
*)

let statement =
  `!b h:real.
     &0 < b /\
     &0 < h /\
     b pow 2 + h pow 2 = (&2) pow 2 /\
     b * h = (&1 / &2) * b * (&1 - h / &2)
     ==> h = &2 / &5`;;

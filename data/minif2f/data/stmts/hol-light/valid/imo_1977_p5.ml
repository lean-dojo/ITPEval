(*
  Statement-only formalization of miniF2F valid problem imo_1977_p5. This file contains no
  proof.
*)

(*
  miniF2F valid artifact imo_1977_p5: natural numbers a, b, q, and r
  satisfying the stated quotient-remainder equations with q^2 + r = 1977
  have integer distances from 22 equal to 15 and 28 in either order.
  This is a statement-only formalization and contains no proof.
*)

let imo_1977_p5 =
  `!a b q r:num.
     r < a + b /\
     a EXP 2 + b EXP 2 = (a + b) * q + r /\
     q EXP 2 + r = 1977
     ==> (abs (int_of_num a - &22) = &15 /\
          abs (int_of_num b - &22) = &28) \/
         (abs (int_of_num a - &22) = &28 /\
          abs (int_of_num b - &22) = &15)`;;

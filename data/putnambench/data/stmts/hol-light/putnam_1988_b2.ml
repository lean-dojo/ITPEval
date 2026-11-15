(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1988_b2:
  the real inequality implication from y >= 0 and
  y(y + 1) <= (x + 1)^2 to y(y - 1) <= x^2 is true. This file contains no
  proof.
*)

let statement =
  `let putnam_1988_b2_solution = T in
   ((!x y:real.
       &0 <= y /\ y * (y + &1) <= (x + &1) pow 2
       ==> y * (y - &1) <= x pow 2)
    <=> putnam_1988_b2_solution)`;;

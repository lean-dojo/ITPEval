(*
  Statement-only formalization of PutnamBench artifact putnam_1986_a1:
  the maximum value of x^3 - 3x over real x satisfying
  x^4 + 36 <= 13x^2 is 18. This file contains no proof.
*)

let statement =
  `let putnam_1986_a1_solution = &18 in
   let f = \x:real. x pow 3 - &3 * x in
   let S = {x:real | x pow 4 + &36 <= &13 * x pow 2} in
   (!x:real. x IN S ==> f x <= putnam_1986_a1_solution) /\
   (?x:real. x IN S /\ putnam_1986_a1_solution = f x)`;;

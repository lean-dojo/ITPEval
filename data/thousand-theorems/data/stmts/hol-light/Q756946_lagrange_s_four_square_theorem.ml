(*
  Statement-only formalization of Thousand Theorems corpus artifact Q756946,
  "Lagrange's four-square theorem": every natural number is the sum of four
  squares of natural numbers. This file contains no proof.
*)

let Q756946_LAGRANGES_FOUR_SQUARE_THEOREM =
  `!n:num. ?a b c d:num.
     a EXP 2 + b EXP 2 + c EXP 2 + d EXP 2 = n`;;

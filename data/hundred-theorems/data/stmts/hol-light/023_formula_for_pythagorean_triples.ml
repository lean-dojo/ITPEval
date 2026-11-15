(*
  Statement-only formalization of "Formula for Pythagorean Triples" from Hundred Theorems
  item 023, classifying integer solutions of x^2 + y^2 = z^2. This file contains no proof.
*)

let FORMULA_FOR_PYTHAGOREAN_TRIPLES =
  `!x y z:int.
      x pow 2 + y pow 2 = z pow 2 <=>
      ?k m n:int.
        ((x = k * (m pow 2 - n pow 2) /\
          y = k * (&2 * m * n)) \/
         (x = k * (&2 * m * n) /\
          y = k * (m pow 2 - n pow 2))) /\
        (z = k * (m pow 2 + n pow 2) \/
         z = --k * (m pow 2 + n pow 2))`;;

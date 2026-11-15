(*
  Statement-only formalization of PutnamBench artifact putnam_1971_a2:
  the identity polynomial is the unique real polynomial satisfying
  P(0) = 0 and P(x^2 + 1) = P(x)^2 + 1 for every real x.
  This file contains no proof.
*)

let statement =
  `let eval =
     \p:real list. \x:real.
       ITLIST (\c acc. c + x * acc) p (&0) in
   !p:real list.
     (eval p (&0) = &0 /\
      (!x:real.
         eval p (x pow 2 + &1) = (eval p x) pow 2 + &1))
     <=>
     (!x:real. eval p x = x)`;;

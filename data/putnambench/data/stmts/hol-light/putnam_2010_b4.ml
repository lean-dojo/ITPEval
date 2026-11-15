(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_b4:
  classification of pairs of real polynomials satisfying a unit forward-shift
  determinant identity. This file contains no proof.
*)

let statement =
  `let eval =
     \p:real list. \x:real.
       ITLIST (\c acc. c + x * acc) p (&0) in
   !p q:real list.
     ((!x:real.
         eval p x * eval q (x + &1) -
         eval p (x + &1) * eval q x = &1)
      <=>
      (?a b c d:real.
         b * c - a * d = &1 /\
         (!x:real. eval p x = a * x + b) /\
         (!x:real. eval q x = c * x + d)))`;;

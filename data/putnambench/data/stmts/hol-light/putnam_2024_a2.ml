(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_a2
  (putnambench__hol-light__putnam_2024_a2): classification of the real
  polynomials p for which p(p(x)) - x is divisible by (p(x) - x)^2.
  This file contains no proof.
*)

let statement =
  `!p:real->real.
     polynomial_function p
     ==>
     ((?q:real->real.
         polynomial_function q /\
         (!x:real.
            p (p x) - x = (p x - x) pow 2 * q x))
      <=>
      ?a:real.
        (!x:real. p x = x + a) \/
        (!x:real. p x = --x + a))`;;

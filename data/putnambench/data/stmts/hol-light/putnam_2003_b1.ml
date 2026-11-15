(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_b1:
  no four real univariate polynomials satisfy the stated separated-product
  identity for 1 + x*y + x^2*y^2. This file contains no proof.
*)

let statement =
  `~(?a b c d:real->real.
       polynomial_function a /\
       polynomial_function b /\
       polynomial_function c /\
       polynomial_function d /\
       (!x y:real.
          &1 + x * y + x pow 2 * y pow 2 =
          a x * c y + b x * d y))`;;

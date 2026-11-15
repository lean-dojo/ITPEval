(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1992_b2:
  the coefficient of x^k in (1 + x + x^2 + x^3)^n as a finite sum of
  products of binomial coefficients. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory pred_setTheory;

val putnam_1992_b2 =
  ``let base =
      \i : num. if i <= 3 then 1 else 0
    in
      let multiply =
        \p q : num -> num.
          \m : num.
            SIGMA
              (\i : num. p i * q (m - i))
              (count (SUC m))
      in
        let one =
          \i : num. if i = 0 then 1 else 0
        in
          !Q : num -> num -> num.
            Q =
              (\n k : num.
                 FUNPOW
                   (\p : num -> num. multiply p base)
                   n
                   one
                   k)
            ==>
            !n k : num.
              Q n k =
              SIGMA
                (\j : num.
                   binomial n j *
                   (if 2 * j <= k
                    then binomial n (k - 2 * j)
                    else 0))
                (count (SUC k))``;

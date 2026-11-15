(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2019_a5:
  the greatest power of X - 1 dividing the polynomial over the prime field
  with coefficients k^((p-1)/2) is (p-1)/2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;
open groupTheory ringTheory;

val putnam_2019_a5 =
  ``!p : num.
      ODD p /\ prime p
      ==>
      let is_poly =
        \f : num -> num.
          (!k : num. f k < p) /\
          FINITE {k : num | f k <> 0}
      in
      let q =
        \k : num.
          if 1 <= k /\ k <= p - 1
          then k ** ((p - 1) DIV 2) MOD p
          else 0
      in
      let poly_one =
        \k : num. if k = 0 then 1 else 0
      in
      let x_minus_one =
        \k : num.
          if k = 0 then p - 1
          else if k = 1 then 1
          else 0
      in
      let poly_mul =
        \f g : num -> num.
        \k : num.
          SIGMA
            (\i : num. f i * g (k - i))
            (count (SUC k)) MOD p
      in
      let x_minus_one_pow =
        \n : num. FUNPOW (poly_mul x_minus_one) n poly_one
      in
      let divides_power =
        \n : num.
          ?s : num -> num.
            is_poly s /\
            q = poly_mul s (x_minus_one_pow n)
      in
        divides_power ((p - 1) DIV 2) /\
        !n : num.
          divides_power n
          ==>
          n <= (p - 1) DIV 2``;

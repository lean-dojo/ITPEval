(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2021_a6:
  an integer polynomial with all coefficients zero or one that factors into
  two nonconstant integer polynomials has a composite value at two. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_2021_a6 =
  ``let integer_polynomial =
      \p : num -> int. FINITE {n : num | p n <> 0};
      poly_mul =
        (\p q : num -> int.
           \n : num.
             ITSET
               (\k acc. p k * q (n - k) + acc)
               (count (SUC n))
               (0 : int));
      poly_eval =
        (\p : num -> int.
         \x : int.
           ITSET
             (\n acc. p n * x ** n + acc)
             {n : num | p n <> 0}
             (0 : int))
    in
      !P : num -> int.
        integer_polynomial P /\
        (!n : num. P n = 0 \/ P n = 1) /\
        (?Q R : num -> int.
           integer_polynomial Q /\
           integer_polynomial R /\
           (?n : num. 0 < n /\ Q n <> 0) /\
           (?n : num. 0 < n /\ R n <> 0) /\
           P = poly_mul Q R)
        ==>
        let value = poly_eval P 2
        in
          value <> 0 /\
          value <> 1 /\
          ~prime (Num (ABS value))``;

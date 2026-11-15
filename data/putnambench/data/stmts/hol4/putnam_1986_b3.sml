(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1986_b3:
  coefficientwise Hensel lifting of a factorization of an integer polynomial
  from a prime modulus to an arbitrary positive prime power. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_1986_b3 =
  ``let integer_polynomials =
      {f : num -> int | FINITE {k : num | f k <> 0}};
      poly_one =
        (\k : num. if k = 0 then (1 : int) else 0);
      poly_add =
        (\f g : num -> int.
           \k : num. f k + g k);
      poly_mul =
        (\f g : num -> int.
           \k : num.
             ITSET
               (\i acc. f i * g (k - i) + acc)
               (count (SUC k))
               (0 : int));
      poly_cong =
        (\f g : num -> int.
           \m : int.
             !k : num. m int_divides (f k - g k))
    in
      !n p : num.
      !f g h r s : num -> int.
        0 < n /\
        0 < p /\
        prime p /\
        f IN integer_polynomials /\
        g IN integer_polynomials /\
        h IN integer_polynomials /\
        r IN integer_polynomials /\
        s IN integer_polynomials /\
        poly_cong
          (poly_add (poly_mul r f) (poly_mul s g))
          poly_one
          (int_of_num p) /\
        poly_cong (poly_mul f g) h (int_of_num p)
        ==>
        ?F G : num -> int.
          F IN integer_polynomials /\
          G IN integer_polynomials /\
          poly_cong F f (int_of_num p) /\
          poly_cong G g (int_of_num p) /\
          poly_cong
            (poly_mul F G)
            h
            ((int_of_num p) ** n)``;

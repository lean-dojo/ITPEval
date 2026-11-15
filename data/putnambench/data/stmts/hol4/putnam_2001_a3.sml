(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2001_a3:
  classification of the integer parameters for which the specified quartic
  factors into two nonconstant integer-coefficient polynomials. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_2001_a3 =
  ``let integer_polynomials =
      {f : num -> int | FINITE {k : num | f k <> 0}};
      poly_mul =
        (\f g : num -> int.
           \k : num.
             ITSET
               (\i acc. f i * g (k - i) + acc)
               (count (SUC k))
               (0 : int));
      P =
        (\m : int.
           \k : num.
             if k = 4 then (1 : int)
             else if k = 2 then -(2 * m + 4)
             else if k = 0 then (m - 2) * (m - 2)
             else 0);
      factorable =
        (\m : int.
           ?a b : num -> int.
             a IN integer_polynomials /\
             b IN integer_polynomials /\
             (?i : num. 0 < i /\ a i <> 0) /\
             (?i : num. 0 < i /\ b i <> 0) /\
             poly_mul a b = P m);
      solution =
        (\m : int.
           ?k : int. m = k * k \/ m = 2 * (k * k))
    in
      !m : int. factorable m <=> solution m``;

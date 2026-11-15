(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1983_b6:
  integer-coefficient polynomials whose squared values at a nontrivial
  complex (2^n + 1)-st root of unity sum to -1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory realTheory intrealTheory
     complexTheory;

val putnam_1983_b6 =
  ``let eval_int_poly =
      \coeffs : int list.
      \z : complex.
        FOLDR
          (\a acc. complex_of_real (real_of_int a) + z * acc)
          0 coeffs
    in
      !n : num. !alpha : complex.
        0 < n /\
        alpha pow ((2 : num) ** n + 1) - 1 = 0 /\
        alpha <> 1
        ==>
        ?p q : int list.
          eval_int_poly p alpha pow 2 +
          eval_int_poly q alpha pow 2 = -1``;

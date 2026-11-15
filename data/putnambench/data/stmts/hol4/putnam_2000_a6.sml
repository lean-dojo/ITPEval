(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2000_a6:
  an integer sequence obtained by iterating an integer-coefficient polynomial
  from zero can return to zero at a positive index only if its first or
  second iterate is zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory;

val putnam_2000_a6 =
  ``let eval_int_poly =
      \coeffs : int list.
      \x : int.
        FOLDR (\c acc. c + x * acc) 0 coeffs
    in
      !f : int list. !a : num -> int.
        a 0 = 0 /\
        (!n : num. a (n + 1) = eval_int_poly f (a n))
        ==>
        ((?m : num. 0 < m /\ a m = 0)
         ==>
         a 1 = 0 \/ a 2 = 0)``;

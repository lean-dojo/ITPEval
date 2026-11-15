(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2008_b4:
  an integer polynomial injective modulo the square of a prime on the
  corresponding residue representatives remains injective modulo the cube.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory;

val putnam_2008_b4 =
  ``let eval_int_poly =
      \coeffs : int list.
      \x : int.
        FOLDR (\c acc. c + x * acc) 0 coeffs
    in
      !p : num. !h : int list.
        prime p /\
        (!i j : num.
           i < p EXP 2 /\
           j < p EXP 2 /\
           (int_of_num (p EXP 2)) int_divides
             (eval_int_poly h (int_of_num i) -
              eval_int_poly h (int_of_num j))
           ==>
           i = j)
        ==>
        !i j : num.
          i < p EXP 3 /\
          j < p EXP 3 /\
          (int_of_num (p EXP 3)) int_divides
            (eval_int_poly h (int_of_num i) -
             eval_int_poly h (int_of_num j))
          ==>
          i = j``;

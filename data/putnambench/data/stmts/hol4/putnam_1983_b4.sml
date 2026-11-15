(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1983_b4:
  every positive-integer sequence obtained by repeatedly adding the floor of
  the square root of its current term contains a square. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory realTheory intrealTheory;

val putnam_1983_b4 =
  ``!a : num -> int.
      0 < a 0 /\
      (!n : num.
         a (n + 1) =
           a n + INT_FLOOR (sqrt (real_of_int (a n))))
      ==>
      ?i : num. ?s : int. a i = s ** 2``;

(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1991_b1:
  eventual constancy of the integer sequence obtained by repeatedly adding
  the remainder after subtracting the greatest square, characterized by
  positive square initial values. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val putnam_1991_b1 =
  ``let putnam_1991_b1_solution =
      \A : num. ?x : num. 0 < x /\ A = x EXP 2
    in
      !m S : num -> num. !A : num. !a : num -> num.
        (!n : num.
           m n EXP 2 <= n /\
           !m' : num. m' EXP 2 <= n ==> m' <= m n) /\
        (!n : num. S n = n - m n EXP 2) /\
        a 0 = A /\
        (!k : num. a (k + 1) = a k + S (a k)) /\
        0 < A
        ==>
        ((?K c : num. !k : num. K <= k ==> a k = c) <=>
         putnam_1991_b1_solution A)``;

(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2013_a2:
  the minimum final term in an increasing integer list that makes a positive
  nonsquare integer times the list product a square defines an injective
  function. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory pred_setTheory;

val putnam_2013_a2 =
  ``let S =
      {n : int | 0 < n /\ ~(?m : int. m ** 2 = n)}
    in
    let admissible =
      \n : int. \a : int list.
        a <> [] /\
        n < HD a /\
        (?m : int.
           m ** 2 =
             n * FOLDR (\x acc : int. x * acc) 1 a) /\
        (!i : num.
           SUC i < LENGTH a
           ==>
           EL i a < EL (SUC i) a)
    in
    let T =
      \n : int.
        {r : int |
           ?a : int list.
             admissible n a /\ LAST a = r}
    in
      !f : int -> int.
        (!n : int.
           n IN S
           ==>
           f n IN T n /\
           !r : int. r IN T n ==> f n <= r)
        ==>
        !x y : int.
          x IN S /\ y IN S /\ f x = f y
          ==>
          x = y``;

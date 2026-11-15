(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2002_b3:
  for every integer n greater than one, 1/e minus (1 - 1/n)^n lies strictly
  between 1/(2ne) and 1/(ne), where e = exp 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory transcTheory;

val putnam_2002_b3 =
  ``let e = exp 1 in
    let f =
      \n : int.
        1 / e -
        (1 - 1 / real_of_int n) pow (Num n)
    in
      !n : int.
        n > 1
        ==>
        1 / (2 * real_of_int n * e) < f n /\
        f n < 1 / (real_of_int n * e)``;

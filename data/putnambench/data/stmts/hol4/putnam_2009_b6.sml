(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2009_b6:
  every positive integer is the endpoint of a length-2010 integer sequence
  built from earlier terms by adding a nonnegative power of two or taking the
  remainder of two earlier positive terms. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory;

val putnam_2009_b6 =
  ``!n : num.
      0 < n
      ==>
      ?a : num -> int.
        a 0 = 0 /\
        a 2009 = int_of_num n /\
        !i : num.
          1 <= i /\ i <= 2009
          ==>
          ((?j : num.
              ?k : num.
                j < i /\
                a i = a j + (2 : int) ** k) \/
           (?b : num.
              ?c : num.
                b < i /\
                c < i /\
                0 < a b /\
                0 < a c /\
                a i = a b % a c))``;

(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2000_a2:
  there are arbitrarily large triples of consecutive integers, each of which
  is a sum of two integer squares. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory;

val putnam_2000_a2 =
  ``!n : int.
      ?m : int.
        m > n /\
        (?a b : int. m = a * a + b * b) /\
        (?c d : int. m + 1 = c * c + d * d) /\
        (?e f : int. m + 2 = e * e + f * f)``;

(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2001_a5:
  existence and joint uniqueness of positive integers satisfying the given
  exponential Diophantine equation. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pairTheory;

val putnam_2001_a5 =
  ``?!an : int # num.
      let a = FST an in
      let n = SND an in
        0 < a /\
        0 < n /\
        a ** (n + 1) - (a + 1) ** n = 2001``;

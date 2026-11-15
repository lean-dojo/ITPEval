(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2021_b2:
  the maximum weighted infinite sum of initial geometric means over
  nonnegative real sequences with sum one is 2/3. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory seqTheory
     transcTheory;

val putnam_2021_b2 =
  ``let admissible =
      \a : num -> real.
        (!k : num. 0 <= a k) /\
        a sums 1
    in
    let term =
      \a : num -> real.
      \n : num.
        (&(SUC n) : real) / ((2 : real) pow (SUC n)) *
        (REAL_PROD_IMAGE a (count (SUC n))) powr
          (1 / (&(SUC n) : real))
    in
    let attainable =
      \S : real.
        ?a : num -> real.
          admissible a /\ (term a sums S)
    in
    let solution = (2 / 3 : real)
    in
      attainable solution /\
      !S : real. attainable S ==> S <= solution``;

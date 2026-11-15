(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2014_a4:
  the smallest possible probability of zero for a nonnegative integer-valued
  random variable with first three moments 1, 2, and 5 is 1/3. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory seqTheory;

val putnam_2014_a4 =
  ``let admissible =
      \p : num -> real.
        (!n : num. 0 <= p n /\ p n <= 1) /\
        summable p /\
        suminf p = 1 /\
        summable (\n : num. (&n : real) * p n) /\
        suminf (\n : num. (&n : real) * p n) = 1 /\
        summable (\n : num. (&n : real) pow 2 * p n) /\
        suminf (\n : num. (&n : real) pow 2 * p n) = 2 /\
        summable (\n : num. (&n : real) pow 3 * p n) /\
        suminf (\n : num. (&n : real) pow 3 * p n) = 5
    in
    let solution = (1 / 3 : real)
    in
      (!p : num -> real.
         admissible p
         ==>
         solution <= p 0) /\
      (?p : num -> real.
         admissible p /\
         p 0 = solution)``;

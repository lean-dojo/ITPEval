(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1984_a3:
  the punctured limit at a of the determinant quotient for the 2n by 2n real
  matrix whose off-diagonal entries alternate between a and b according to
  index parity is n squared times (a squared minus b squared). This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory fcpTheory realTheory real_topologyTheory;
open determinantTheory;

val putnam_1984_a3 =
  ``!n : num. !a b : real. !Mn : real -> real['N]['N].
      dimindex (:'N) = 2 * n /\
      0 < n /\
      a <> b /\
      Mn =
        (\x : real.
           FCP i j.
             if i = j then x
             else if EVEN (i + j) then a
             else b)
      ==>
      ((\x : real.
          determinant$det (Mn x) / (x - a) pow (2 * n - 2)) -->
       (&n : real) pow 2 * (a pow 2 - b pow 2))
        (at a)``;

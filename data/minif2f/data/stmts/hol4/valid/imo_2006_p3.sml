(*
  Statement-only formalization of miniF2F valid problem imo_2006_p3: a cyclic quartic
  inequality over three arbitrary real variables. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val imo_2006_p3 =
  ``!a b c : real.
      a * b * (a pow 2 - b pow 2) +
        b * c * (b pow 2 - c pow 2) +
        c * a * (c pow 2 - a pow 2) <=
      9 * sqrt 2 / 32 * (a pow 2 + b pow 2 + c pow 2) pow 2``;

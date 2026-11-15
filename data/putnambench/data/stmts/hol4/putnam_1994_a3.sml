(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1994_a3:
  every four-coloring of the closed unit isosceles right triangle has two
  same-colored points at least 2 - sqrt 2 apart. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory transcTheory;

val putnam_1994_a3 =
  ``let triangle =
      {p : real # real |
         0 <= FST p /\ 0 <= SND p /\ FST p + SND p <= 1}
    in
    let dist =
      \p q : real # real.
        sqrt ((FST p - FST q) pow 2 + (SND p - SND q) pow 2)
    in
      !color : (real # real) -> num.
        (!p : real # real. p IN triangle ==> color p < 4)
        ==>
        ?p q : real # real.
          p IN triangle /\
          q IN triangle /\
          color p = color q /\
          2 - sqrt 2 <= dist p q``;

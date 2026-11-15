(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1998_b1:
  the displayed rational expression in a positive real variable has minimum
  value 6. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val putnam_1998_b1 =
  ``let objective =
      \x : real.
        ((x + 1 / x) pow 6 - (x pow 6 + 1 / (x pow 6)) - 2) /
        ((x + 1 / x) pow 3 + (x pow 3 + 1 / (x pow 3)))
    in
      (!x : real. 0 < x ==> 6 <= objective x) /\
      (?x : real. 0 < x /\ objective x = 6)``;

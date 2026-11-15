(*
  Statement-only formalization of "Insolvability of General Higher Degree Equations
  (Abel-Ruffini)" from Hundred Theorems item 016. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory complexTheory;

val insolubility_of_general_higher_degree_equations_abel_ruffini =
  ``let obtainable_by_radicals =
      \z : complex.
        !S : complex -> bool.
          (S 0 /\
           S 1 /\
           (!u v : complex.
              S u /\ S v ==> S (u + v) /\ S (u * v)) /\
           (!u : complex.
              S u ==> S (0 - u)) /\
           (!u : complex.
              S u /\ u <> 0 ==> S (1 / u)) /\
           (!n : num. !u v : complex.
              0 < n /\ S u /\ v pow n = u ==> S v))
          ==> S z
    in
      ?x : complex.
        x pow 5 - 4 * x + 2 = 0 /\
        ~obtainable_by_radicals x``;

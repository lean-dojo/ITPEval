(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1139041, "Cauchy's theorem (group theory)": if a prime divides the
  cardinality of a finite group, the group contains an element of that prime
  order. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory groupTheory pred_setTheory;

val exists_prime_orderOf_dvd_card =
  ``!(g : 'a group) (p : num).
      Group g /\
      FINITE g.carrier /\
      prime p /\
      p divides CARD g.carrier
      ==>
      ?x : 'a.
        x IN g.carrier /\
        order g x = p``;

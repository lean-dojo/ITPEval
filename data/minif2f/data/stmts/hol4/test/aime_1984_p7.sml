(*
  Statement-only formalization of miniF2F test problem aime_1984_p7: a natural-number
  functional equation determining f 84 from a threshold rule and positive-input recursion.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val _ = new_theory "hello";

val aime_1984_p7 =
  ``!f : num -> num.
      (!n. 1000 <= n ==> f n = n - 3) /\
      (!n. 0 < n /\ n < 1000 ==> f n = f (f (n + 5)))
      ==>
      f 84 = 997``;

val _ = export_theory();

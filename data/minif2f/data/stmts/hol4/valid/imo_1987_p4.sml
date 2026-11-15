(*
  Statement-only formalization of miniF2F valid problem imo_1987_p4: every natural-number
  self-map has an input where its second iterate differs from adding 1987. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val _ = new_theory "hello";

val imo_1987_p4 =
  ``!f : num -> num.
      ?n : num. f (f n) <> n + 1987``;

val _ = export_theory();

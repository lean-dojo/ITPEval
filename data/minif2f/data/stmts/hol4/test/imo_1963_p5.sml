(*
  Statement-only formalization of miniF2F test problem imo_1963_p5: the real
  cosine identity at pi/7, 2*pi/7, and 3*pi/7. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val _ = new_theory "hello";

val imo_1963_p5 =
  ``cos (pi / 7) - cos (2 * pi / 7) + cos (3 * pi / 7) = 1 / 2``;

val _ = export_theory();

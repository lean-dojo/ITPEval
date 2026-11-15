(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_73: over the complex
  numbers, equality of two paired products with x distinct from r implies x = p + q - r.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open complexTheory;

val mathd_algebra_73 =
  ``!p q r x : complex.
      ((x - p) * (x - q) = (r - p) * (r - q)) /\
      x <> r
      ==>
      x = p + q - r``;

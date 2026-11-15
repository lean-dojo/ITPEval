(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_140:
  deriving a coefficient relation from a real polynomial factorization
  identity with positive parameters. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_140 =
  ``!a b c : real.
      0 < a /\
      0 < b /\
      0 < c /\
      (!x : real.
         24 * x pow 2 - 19 * x - 35 =
         (a * x - 5) * (2 * (b * x) + c))
      ==>
      a * b - 3 * c = -9``;

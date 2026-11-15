(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q4116459, "Niven's theorem": if a real angle is a rational multiple of pi
  and has rational cosine, then its cosine is one of -1, -1/2, 0, 1/2, or 1.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open ratTheory realTheory real_of_ratTheory transcTheory;

val niven =
  ``!theta : real.
      (?r : rat. theta = real_of_rat r * pi) /\
      (?q : rat. cos theta = real_of_rat q)
      ==>
      cos theta = -1 \/
      cos theta = -(1 / 2) \/
      cos theta = 0 \/
      cos theta = 1 / 2 \/
      cos theta = 1``;

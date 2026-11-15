(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q853067, "Solutions to Pell's equation": every natural-number solution of
  x^2 - (a^2 - 1)y^2 = 1 for a > 1 occurs in the recursively defined Pell
  sequence starting at (1,0). This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory pairTheory;

val q853067_pell_def = Define`
  (q853067_pell (a : num) 0 = (1, 0)) /\
  (q853067_pell a (SUC n) =
     (FST (q853067_pell a n) * a +
        (a * a - 1) * SND (q853067_pell a n),
      FST (q853067_pell a n) +
        SND (q853067_pell a n) * a))`;

val q853067_xn_def = new_definition (
  "q853067_xn_def",
  ``q853067_xn (a : num) (n : num) = FST (q853067_pell a n)``);

val q853067_yn_def = new_definition (
  "q853067_yn_def",
  ``q853067_yn (a : num) (n : num) = SND (q853067_pell a n)``);

val solutions_to_pell_s_equation =
  ``!a x y : num.
      1 < a
      ==>
      x * x - (a * a - 1) * y * y = 1
      ==>
      ?n : num.
        x = q853067_xn a n /\
        y = q853067_yn a n``;

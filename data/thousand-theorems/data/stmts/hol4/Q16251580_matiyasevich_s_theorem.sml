(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q16251580, "Matiyasevich's theorem": membership in the recursively defined
  Pell sequence is equivalent to a system of natural-number Pell equations,
  divisibility conditions, and modular congruences. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory dividesTheory pairTheory;

val q16251580_pell_def = Define`
  (q16251580_pell (a : num) 0 = (1, 0)) /\
  (q16251580_pell a (SUC n) =
     (FST (q16251580_pell a n) * a +
        (a * a - 1) * SND (q16251580_pell a n),
      FST (q16251580_pell a n) +
        SND (q16251580_pell a n) * a))`;

val matiyasevich_theorem =
  ``!a k x y : num.
      (1 < a /\
       FST (q16251580_pell a k) = x /\
       SND (q16251580_pell a k) = y)
      <=>
      1 < a /\
      k <= y /\
      ((x = 1 /\ y = 0) \/
       ?u v s t b : num.
         x * x - (a * a - 1) * y * y = 1 /\
         u * u - (a * a - 1) * v * v = 1 /\
         s * s - (b * b - 1) * t * t = 1 /\
         1 < b /\
         b MOD (4 * y) = 1 MOD (4 * y) /\
         b MOD u = a MOD u /\
         0 < v /\
         divides (y * y) v /\
         s MOD u = x MOD u /\
         t MOD (4 * y) = k MOD (4 * y))``;

(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q2919401, "Ostrowski's theorem": every nontrivial real-valued absolute
  value on the rationals is equivalent either to the usual Archimedean
  absolute value or uniquely to a p-adic absolute value. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory integerTheory primeTheory ratTheory
     realTheory real_of_ratTheory transcTheory;

val q2919401_absolute_value_def = new_definition (
  "q2919401_absolute_value_def",
  ``q2919401_absolute_value (f : rat -> real) <=>
      (!q. 0 <= f q) /\
      (!q. (f q = 0 <=> q = 0q)) /\
      (!q r. f (q * r) = f q * f r) /\
      (!q r. f (q + r) <= f q + f r)``);

val q2919401_nontrivial_def = new_definition (
  "q2919401_nontrivial_def",
  ``q2919401_nontrivial (f : rat -> real) <=>
      ?q : rat. q <> 0q /\ f q <> 1``);

val q2919401_equiv_def = new_definition (
  "q2919401_equiv_def",
  ``q2919401_equiv (f : rat -> real) (g : rat -> real) <=>
      ?c : real. 0 < c /\ !q : rat. f q powr c = g q``);

val q2919401_real_def = new_definition (
  "q2919401_real_def",
  ``q2919401_real (q : rat) = abs (real_of_rat q)``);

val q2919401_padic_def = new_definition (
  "q2919401_padic_def",
  ``q2919401_padic (p : num) (q : rat) =
      if q = 0q then 0
      else
        ((&p : real) pow prime_power_index p (RATD q)) /
        ((&p : real) pow prime_power_index p (Num (RATN q)))``);

val equiv_real_or_padic =
  ``!f : rat -> real.
      q2919401_absolute_value f /\
      q2919401_nontrivial f
      ==>
      q2919401_equiv f q2919401_real \/
      ?!p : num.
        prime p /\
        q2919401_equiv f (q2919401_padic p)``;

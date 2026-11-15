(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q2734084 (thousand-theorems__hol4__Q2734084), "Bohr–Mollerup theorem":
  a positive log-convex real function satisfying the Gamma functional equation
  and normalized at one equals the Gamma function on the positive reals. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open seqTheory transcTheory derivativeTheory;

val q2734084_gamma_seq_def = new_definition (
  "q2734084_gamma_seq_def",
  ``q2734084_gamma_seq (x : real) (n : num) =
      if n = 0 then 0
      else
        ((&n : real) rpow x) * &(FACT n) /
          real_sigma$product (count (n + 1)) (\m. x + &m)``);

val q2734084_gamma_def = new_definition (
  "q2734084_gamma_def",
  ``q2734084_gamma (x : real) =
      lim (q2734084_gamma_seq x)``);

val bohr_mollerup_theorem =
  ``!f : real -> real.
      (ln o f) convex_on {x : real | 0 < x} /\
      (!y. 0 < y ==> f (y + 1) = y * f y) /\
      (!y. 0 < y ==> 0 < f y) /\
      f 1 = 1
      ==>
      !x. 0 < x ==> f x = q2734084_gamma x``;

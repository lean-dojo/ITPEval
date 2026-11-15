(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q727102 (thousand-theorems__hol4__Q727102), "Fermat's theorem (stationary
  points)": the totalized Frechet derivative of a real-valued function at a
  local extremum is zero, both on an arbitrary real normed vector space and
  for a real function of one real variable. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val q727102_real_normed_space_def = new_definition (
  "q727102_real_normed_space_def",
  ``q727102_real_normed_space
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (norm : 'e -> real) <=>
      (!x y z. add x (add y z) = add (add x y) z) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x. smul 1 x = x) /\
      (!a b x. smul (a * b) x = smul a (smul b x)) /\
      (!a b x. smul (a + b) x = add (smul a x) (smul b x)) /\
      (!a x y. smul a (add x y) = add (smul a x) (smul a y)) /\
      (!x. 0 <= norm x) /\
      (!x. norm x = 0 <=> x = zero) /\
      (!x y. norm (add x y) <= norm x + norm y) /\
      (!a x. norm (smul a x) = abs a * norm x)``);

val q727102_continuous_linear_functional_def = new_definition (
  "q727102_continuous_linear_functional_def",
  ``q727102_continuous_linear_functional
      (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e)
      (norm : 'e -> real) (L : 'e -> real) <=>
      (!x y. L (add x y) = L x + L y) /\
      (!c x. L (smul c x) = c * L x) /\
      ?C : real.
        0 <= C /\
        !x. abs (L x) <= C * norm x``);

val q727102_has_fderiv_at_def = new_definition (
  "q727102_has_fderiv_at_def",
  ``q727102_has_fderiv_at
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (norm : 'e -> real)
      (f : 'e -> real) (L : 'e -> real) (a : 'e) <=>
      q727102_continuous_linear_functional add smul norm L /\
      !epsilon : real.
        0 < epsilon ==>
        ?delta : real.
          0 < delta /\
          !x : 'e.
            norm (add x (neg a)) < delta ==>
            abs
              (f x - f a - L (add x (neg a))) <=
            epsilon * norm (add x (neg a))``);

val q727102_fderiv_def = new_definition (
  "q727102_fderiv_def",
  ``q727102_fderiv
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (norm : 'e -> real)
      (f : 'e -> real) (a : 'e) =
      if ?L : 'e -> real.
           q727102_has_fderiv_at add neg smul norm f L a
      then
        @L. q727102_has_fderiv_at add neg smul norm f L a
      else
        \x : 'e. 0``);

val q727102_is_local_min_def = new_definition (
  "q727102_is_local_min_def",
  ``q727102_is_local_min
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (f : 'e -> real) (a : 'e) <=>
      ?radius : real.
        0 < radius /\
        !x : 'e.
          norm (add x (neg a)) < radius ==>
          f a <= f x``);

val q727102_is_local_max_def = new_definition (
  "q727102_is_local_max_def",
  ``q727102_is_local_max
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (f : 'e -> real) (a : 'e) <=>
      ?radius : real.
        0 < radius /\
        !x : 'e.
          norm (add x (neg a)) < radius ==>
          f x <= f a``);

val q727102_is_local_extr_def = new_definition (
  "q727102_is_local_extr_def",
  ``q727102_is_local_extr
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (f : 'e -> real) (a : 'e) <=>
      q727102_is_local_min add neg norm f a \/
      q727102_is_local_max add neg norm f a``);

val IsLocalExtr_fderiv_eq_zero =
  ``!(zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (norm : 'e -> real)
      (f : 'e -> real) (a : 'e).
      q727102_real_normed_space zero add neg smul norm /\
      q727102_is_local_extr add neg norm f a
      ==>
      q727102_fderiv add neg smul norm f a = (\x : 'e. 0)``;

val q727102_has_deriv_at_def = new_definition (
  "q727102_has_deriv_at_def",
  ``q727102_has_deriv_at
      (f : real -> real) (fprime : real) (a : real) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?delta : real.
          0 < delta /\
          !x : real.
            abs (x - a) < delta ==>
            abs (f x - f a - fprime * (x - a)) <=
              epsilon * abs (x - a)``);

val q727102_deriv_def = new_definition (
  "q727102_deriv_def",
  ``q727102_deriv (f : real -> real) (a : real) =
      if ?fprime : real. q727102_has_deriv_at f fprime a
      then @fprime. q727102_has_deriv_at f fprime a
      else 0``);

val q727102_is_real_local_extr_def = new_definition (
  "q727102_is_real_local_extr_def",
  ``q727102_is_real_local_extr
      (f : real -> real) (a : real) <=>
      (?radius : real.
        0 < radius /\
        !x : real. abs (x - a) < radius ==> f a <= f x) \/
      (?radius : real.
        0 < radius /\
        !x : real. abs (x - a) < radius ==> f x <= f a)``);

val IsLocalExtr_deriv_eq_zero =
  ``!(f : real -> real) (a : real).
      q727102_is_real_local_extr f a ==>
      q727102_deriv f a = 0``;

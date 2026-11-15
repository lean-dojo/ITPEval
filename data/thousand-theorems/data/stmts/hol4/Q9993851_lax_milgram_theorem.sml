(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q9993851 (thousand-theorems__hol4__Q9993851), "Lax–Milgram theorem":
  every bounded coercive bilinear form on a complete real inner-product space
  induces a continuous linear equivalence representing the form through the
  inner product. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory transcTheory;

val q9993851_real_inner_product_space_def = new_definition (
  "q9993851_real_inner_product_space_def",
  ``q9993851_real_inner_product_space
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (inner : 'e -> 'e -> real) <=>
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x. smul 1 x = x) /\
      (!a b x. smul (a * b) x = smul a (smul b x)) /\
      (!a b x. smul (a + b) x = add (smul a x) (smul b x)) /\
      (!a x y. smul a (add x y) = add (smul a x) (smul a y)) /\
      (!x. smul 0 x = zero) /\
      (!a. smul a zero = zero) /\
      (!x y. inner x y = inner y x) /\
      (!x y z. inner (add x y) z = inner x z + inner y z) /\
      (!a x y. inner (smul a x) y = a * inner x y) /\
      (!x. 0 <= inner x x) /\
      (!x. (inner x x = 0) <=> (x = zero))``);

val q9993851_norm_def = new_definition (
  "q9993851_norm_def",
  ``q9993851_norm (inner : 'e -> 'e -> real) (x : 'e) =
      sqrt (inner x x)``);

val q9993851_cauchy_def = new_definition (
  "q9993851_cauchy_def",
  ``q9993851_cauchy
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (inner : 'e -> 'e -> real) (u : num -> 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !m n : num.
          N <= m /\ N <= n ==>
          q9993851_norm inner
            (add (u m) (neg (u n))) < epsilon``);

val q9993851_tendsto_def = new_definition (
  "q9993851_tendsto_def",
  ``q9993851_tendsto
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (inner : 'e -> 'e -> real) (u : num -> 'e) (x : 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !n : num.
          N <= n ==>
          q9993851_norm inner
            (add (u n) (neg x)) < epsilon``);

val q9993851_complete_def = new_definition (
  "q9993851_complete_def",
  ``q9993851_complete
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (inner : 'e -> 'e -> real) <=>
      !u : num -> 'e.
        q9993851_cauchy add neg inner u ==>
        ?x : 'e. q9993851_tendsto add neg inner u x``);

val q9993851_bounded_bilinear_form_def = new_definition (
  "q9993851_bounded_bilinear_form_def",
  ``q9993851_bounded_bilinear_form
      (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e)
      (inner : 'e -> 'e -> real) (B : 'e -> 'e -> real) <=>
      (!x y z. B (add x y) z = B x z + B y z) /\
      (!a x y. B (smul a x) y = a * B x y) /\
      (!x y z. B x (add y z) = B x y + B x z) /\
      (!a x y. B x (smul a y) = a * B x y) /\
      ?M : real.
        0 <= M /\
        !x y.
          abs (B x y) <=
          M * q9993851_norm inner x * q9993851_norm inner y``);

val q9993851_coercive_def = new_definition (
  "q9993851_coercive_def",
  ``q9993851_coercive
      (inner : 'e -> 'e -> real) (B : 'e -> 'e -> real) <=>
      ?C : real.
        0 < C /\
        !u.
          C * q9993851_norm inner u * q9993851_norm inner u <=
          B u u``);

val q9993851_continuous_linear_map_def = new_definition (
  "q9993851_continuous_linear_map_def",
  ``q9993851_continuous_linear_map
      (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e)
      (inner : 'e -> 'e -> real) (L : 'e -> 'e) <=>
      (!x y. L (add x y) = add (L x) (L y)) /\
      (!a x. L (smul a x) = smul a (L x)) /\
      ?K : real.
        0 <= K /\
        !x.
          q9993851_norm inner (L x) <=
          K * q9993851_norm inner x``);

val q9993851_continuous_linear_equiv_def = new_definition (
  "q9993851_continuous_linear_equiv_def",
  ``q9993851_continuous_linear_equiv
      (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e)
      (inner : 'e -> 'e -> real)
      (forward : 'e -> 'e) (inverse : 'e -> 'e) <=>
      q9993851_continuous_linear_map add smul inner forward /\
      q9993851_continuous_linear_map add smul inner inverse /\
      (!x. inverse (forward x) = x) /\
      (!x. forward (inverse x) = x)``);

val IsCoercive_continuousLinearEquivOfBilin =
  ``!(zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (inner : 'e -> 'e -> real)
      (B : 'e -> 'e -> real).
      q9993851_real_inner_product_space zero add neg smul inner /\
      q9993851_complete add neg inner /\
      q9993851_bounded_bilinear_form add smul inner B /\
      q9993851_coercive inner B
      ==>
      ?forward inverse : 'e -> 'e.
        q9993851_continuous_linear_equiv
          add smul inner forward inverse /\
        !v w. inner (forward v) w = B v w``;

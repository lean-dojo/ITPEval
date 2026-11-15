(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1217677, "Fundamental theorem of calculus": Banach-valued interval
  integrals have the expected strict derivative at an almost-everywhere
  Lebesgue point, and integrate a continuous function's right derivative to
  its endpoint difference. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory extrealTheory;
open topologyTheory real_topologyTheory measureTheory borelTheory lebesgueTheory;

val q1217677_real_normed_space_def = new_definition (
  "q1217677_real_normed_space_def",
  ``q1217677_real_normed_space
      (zero : 'g) (add : 'g -> 'g -> 'g) (neg : 'g -> 'g)
      (smul : real -> 'g -> 'g) (norm : 'g -> real) <=>
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

val q1217677_tendsto_seq_def = new_definition (
  "q1217677_tendsto_seq_def",
  ``q1217677_tendsto_seq
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g) (norm : 'g -> real)
      (u : num -> 'g) (ell : 'g) <=>
      !epsilon.
        0 < epsilon ==>
        ?N. !n. N <= n ==> norm (add (u n) (neg ell)) < epsilon``);

val q1217677_cauchy_def = new_definition (
  "q1217677_cauchy_def",
  ``q1217677_cauchy
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g) (norm : 'g -> real)
      (u : num -> 'g) <=>
      !epsilon.
        0 < epsilon ==>
        ?N. !p q. N <= p /\ N <= q ==>
          norm (add (u p) (neg (u q))) < epsilon``);

val q1217677_complete_def = new_definition (
  "q1217677_complete_def",
  ``q1217677_complete
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g) (norm : 'g -> real) <=>
      !u : num -> 'g.
        q1217677_cauchy add neg norm u ==>
        ?ell. q1217677_tendsto_seq add neg norm u ell``);

val q1217677_measurable_simple_on_def = new_definition (
  "q1217677_measurable_simple_on_def",
  ``q1217677_measurable_simple_on
      (s : real set) (phi : real -> 'g) <=>
      FINITE (IMAGE phi s) /\
      !y : 'g. {x | x IN s /\ phi x = y} IN measurable_sets lborel``);

val q1217677_strongly_measurable_on_def = new_definition (
  "q1217677_strongly_measurable_on_def",
  ``q1217677_strongly_measurable_on
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g) (norm : 'g -> real)
      (s : real set) (f : real -> 'g) <=>
      ?phi : num -> real -> 'g.
        (!n. q1217677_measurable_simple_on s (phi n)) /\
        !x. x IN s ==>
          q1217677_tendsto_seq add neg norm (\n. phi n x) (f x)``);

val q1217677_ae_strongly_measurable_on_def = new_definition (
  "q1217677_ae_strongly_measurable_on_def",
  ``q1217677_ae_strongly_measurable_on
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g) (norm : 'g -> real)
      (s : real set) (f : real -> 'g) <=>
      ?g : real -> 'g.
        q1217677_strongly_measurable_on add neg norm s g /\
        (AE x::lborel. x IN s ==> f x = g x)``);

val q1217677_bochner_integrable_on_def = new_definition (
  "q1217677_bochner_integrable_on_def",
  ``q1217677_bochner_integrable_on
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g) (norm : 'g -> real)
      (s : real set) (f : real -> 'g) <=>
      ?g : real -> 'g.
        q1217677_strongly_measurable_on add neg norm s g /\
        integrable lborel
          (Normal o (\x. if x IN s then norm (g x) else 0)) /\
        (AE x::lborel. x IN s ==> f x = g x)``);

val q1217677_simple_integral_on_def = new_definition (
  "q1217677_simple_integral_on_def",
  ``q1217677_simple_integral_on
      (zero : 'g) (add : 'g -> 'g -> 'g)
      (smul : real -> 'g -> 'g) (s : real set) (phi : real -> 'g) =
      ITSET
        (\y acc.
          add
            (smul
              (real (measure lborel {x | x IN s /\ phi x = y})) y)
            acc)
        (IMAGE phi s) zero``);

val q1217677_bochner_approximates_on_def = new_definition (
  "q1217677_bochner_approximates_on_def",
  ``q1217677_bochner_approximates_on
      (zero : 'g) (add : 'g -> 'g -> 'g) (neg : 'g -> 'g)
      (smul : real -> 'g -> 'g) (norm : 'g -> real)
      (s : real set) (f : real -> 'g)
      (phi : num -> real -> 'g) (ell : 'g) <=>
      ?g : real -> 'g.
        q1217677_strongly_measurable_on add neg norm s g /\
        integrable lborel
          (Normal o (\x. if x IN s then norm (g x) else 0)) /\
        (AE x::lborel. x IN s ==> f x = g x) /\
        (!n. q1217677_measurable_simple_on s (phi n)) /\
        (!n.
          integrable lborel
            (Normal o
              (\x. if x IN s then norm (phi n x) else 0))) /\
        (!n.
          integrable lborel
            (Normal o
              (\x.
                if x IN s
                then norm (add (phi n x) (neg (g x)))
                else 0))) /\
        (((\n.
            real
              (integral lborel
                (Normal o
                  (\x.
                    if x IN s
                    then norm (add (phi n x) (neg (g x)))
                    else 0)))) -->
          0) sequentially) /\
        q1217677_tendsto_seq add neg norm
          (\n. q1217677_simple_integral_on zero add smul s (phi n))
          ell``);

val q1217677_bochner_integral_on_def = new_definition (
  "q1217677_bochner_integral_on_def",
  ``q1217677_bochner_integral_on
      (zero : 'g) (add : 'g -> 'g -> 'g) (neg : 'g -> 'g)
      (smul : real -> 'g -> 'g) (norm : 'g -> real)
      (s : real set) (f : real -> 'g) =
      if q1217677_complete add neg norm /\
         q1217677_bochner_integrable_on add neg norm s f
      then
        @ell.
          ?phi : num -> real -> 'g.
            q1217677_bochner_approximates_on
              zero add neg smul norm s f phi ell
      else
        zero``);

val q1217677_interval_integrable_def = new_definition (
  "q1217677_interval_integrable_def",
  ``q1217677_interval_integrable
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g) (norm : 'g -> real)
      (f : real -> 'g) (a : real) (b : real) <=>
      q1217677_bochner_integrable_on add neg norm (interval (a,b)) f /\
      q1217677_bochner_integrable_on add neg norm (interval (b,a)) f``);

val q1217677_interval_integral_def = new_definition (
  "q1217677_interval_integral_def",
  ``q1217677_interval_integral
      (zero : 'g) (add : 'g -> 'g -> 'g) (neg : 'g -> 'g)
      (smul : real -> 'g -> 'g) (norm : 'g -> real)
      (f : real -> 'g) (a : real) (b : real) =
      if a <= b
      then
        q1217677_bochner_integral_on
          zero add neg smul norm (interval (a,b)) f
      else
        neg
          (q1217677_bochner_integral_on
            zero add neg smul norm (interval (b,a)) f)``);

val q1217677_strongly_measurable_at_def = new_definition (
  "q1217677_strongly_measurable_at_def",
  ``q1217677_strongly_measurable_at
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g) (norm : 'g -> real)
      (f : real -> 'g) (b : real) <=>
      ?delta.
        0 < delta /\
        q1217677_ae_strongly_measurable_on add neg norm
          (interval (b - delta,b + delta)) f``);

val q1217677_tendsto_ae_at_def = new_definition (
  "q1217677_tendsto_ae_at_def",
  ``q1217677_tendsto_ae_at
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g) (norm : 'g -> real)
      (f : real -> 'g) (b : real) (c : 'g) <=>
      !epsilon.
        0 < epsilon ==>
        ?delta.
          0 < delta /\
          (AE x::lborel.
            abs (x - b) < delta ==>
            norm (add (f x) (neg c)) < epsilon)``);

val q1217677_has_strict_derivative_at_def = new_definition (
  "q1217677_has_strict_derivative_at_def",
  ``q1217677_has_strict_derivative_at
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g)
      (smul : real -> 'g -> 'g) (norm : 'g -> real)
      (primitive : real -> 'g) (c : 'g) (b : real) <=>
      !epsilon.
        0 < epsilon ==>
        ?delta.
          0 < delta /\
          !x y.
            abs (x - b) < delta /\
            abs (y - b) < delta /\
            x <> y ==>
            norm
              (add
                (add (primitive x) (neg (primitive y)))
                (neg (smul (x - y) c))) <
            epsilon * abs (x - y)``);

val q1217677_continuous_on_closed_interval_def = new_definition (
  "q1217677_continuous_on_closed_interval_def",
  ``q1217677_continuous_on_closed_interval
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g) (norm : 'g -> real)
      (f : real -> 'g) (a : real) (b : real) <=>
      !x.
        a <= x /\ x <= b ==>
        !epsilon.
          0 < epsilon ==>
          ?delta.
            0 < delta /\
            !y.
              a <= y /\ y <= b /\ abs (y - x) < delta ==>
              norm (add (f y) (neg (f x))) < epsilon``);

val q1217677_has_right_derivative_at_def = new_definition (
  "q1217677_has_right_derivative_at_def",
  ``q1217677_has_right_derivative_at
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g)
      (smul : real -> 'g -> 'g) (norm : 'g -> real)
      (f : real -> 'g) (f' : 'g) (x : real) <=>
      !epsilon.
        0 < epsilon ==>
        ?delta.
          0 < delta /\
          !y.
            x < y /\ y - x < delta ==>
            norm
              (add
                (add (f y) (neg (f x)))
                (neg (smul (y - x) f'))) <
            epsilon * abs (y - x)``);

val intervalIntegral_integral_hasStrictDerivAt_of_tendsto_ae_right =
  ``!(zero : 'g) (add : 'g -> 'g -> 'g) (neg : 'g -> 'g)
      (smul : real -> 'g -> 'g) (norm : 'g -> real)
      (f : real -> 'g) (c : 'g) (a : real) (b : real).
      q1217677_real_normed_space zero add neg smul norm /\
      q1217677_complete add neg norm /\
      q1217677_interval_integrable add neg norm f a b /\
      q1217677_strongly_measurable_at add neg norm f b /\
      q1217677_tendsto_ae_at add neg norm f b c
      ==>
      q1217677_has_strict_derivative_at add neg smul norm
        (\u.
          q1217677_interval_integral
            zero add neg smul norm f a u)
        c b``;

val intervalIntegral_integral_eq_sub_of_hasDeriv_right_of_le =
  ``!(zero : 'g) (add : 'g -> 'g -> 'g) (neg : 'g -> 'g)
      (smul : real -> 'g -> 'g) (norm : 'g -> real)
      (f : real -> 'g) (f' : real -> 'g) (a : real) (b : real).
      q1217677_real_normed_space zero add neg smul norm /\
      q1217677_complete add neg norm /\
      a <= b /\
      q1217677_continuous_on_closed_interval add neg norm f a b /\
      (!x.
        a < x /\ x < b ==>
        q1217677_has_right_derivative_at
          add neg smul norm f (f' x) x) /\
      q1217677_interval_integrable add neg norm f' a b
      ==>
      q1217677_interval_integral zero add neg smul norm f' a b =
      add (f b) (neg (f a))``;

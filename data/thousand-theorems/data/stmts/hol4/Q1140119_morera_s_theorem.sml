(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1140119 (thousand-theorems__hol4__Q1140119), "Morera's theorem": on an
  open subset of the complex plane, a function into a complete complex
  normed space is continuous with zero integral around every axis-parallel
  rectangle exactly when it is complex differentiable there. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory extrealTheory complexTheory;
open topologyTheory real_topologyTheory measureTheory borelTheory lebesgueTheory;

val q1140119_normed_complex_space_def = new_definition (
  "q1140119_normed_complex_space_def",
  ``q1140119_normed_complex_space
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (smulE : complex -> 'e -> 'e)
      (normE : 'e -> real) <=>
      (!x y z. addE (addE x y) z = addE x (addE y z)) /\
      (!x y. addE x y = addE y x) /\
      (!x. addE zeroE x = x) /\
      (!x. addE (negE x) x = zeroE) /\
      (!x. smulE 1 x = x) /\
      (!a b x. smulE (a * b) x = smulE a (smulE b x)) /\
      (!a b x. smulE (a + b) x = addE (smulE a x) (smulE b x)) /\
      (!a x y. smulE a (addE x y) = addE (smulE a x) (smulE a y)) /\
      (!x. smulE 0 x = zeroE) /\
      (!a. smulE a zeroE = zeroE) /\
      (!x. negE x = smulE (-1) x) /\
      (!x. 0 <= normE x) /\
      (!x. (normE x = 0) <=> (x = zeroE)) /\
      (!x. normE (negE x) = normE x) /\
      (!x y. normE (addE x y) <= normE x + normE y) /\
      (!a x. normE (smulE a x) = modu a * normE x)``);

val q1140119_tendsto_def = new_definition (
  "q1140119_tendsto_def",
  ``q1140119_tendsto
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (normE : 'e -> real) (u : num -> 'e) (x : 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !n : num.
          N <= n ==>
          normE (addE (u n) (negE x)) < epsilon``);

val q1140119_cauchy_def = new_definition (
  "q1140119_cauchy_def",
  ``q1140119_cauchy
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (normE : 'e -> real) (u : num -> 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !m n : num.
          N <= m /\ N <= n ==>
          normE (addE (u m) (negE (u n))) < epsilon``);

val q1140119_complete_def = new_definition (
  "q1140119_complete_def",
  ``q1140119_complete
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (normE : 'e -> real) <=>
      !u : num -> 'e.
        q1140119_cauchy addE negE normE u ==>
        ?x : 'e. q1140119_tendsto addE negE normE u x``);

val q1140119_measurable_simple_on_def = new_definition (
  "q1140119_measurable_simple_on_def",
  ``q1140119_measurable_simple_on
      (s : real set) (phi : real -> 'e) <=>
      FINITE (IMAGE phi s) /\
      !y : 'e. {x | x IN s /\ phi x = y} IN measurable_sets lborel``);

val q1140119_strongly_measurable_on_def = new_definition (
  "q1140119_strongly_measurable_on_def",
  ``q1140119_strongly_measurable_on
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (normE : 'e -> real) (s : real set) (f : real -> 'e) <=>
      ?phi : num -> real -> 'e.
        (!n. q1140119_measurable_simple_on s (phi n)) /\
        !x. x IN s ==>
          q1140119_tendsto addE negE normE (\n. phi n x) (f x)``);

val q1140119_bochner_integrable_on_def = new_definition (
  "q1140119_bochner_integrable_on_def",
  ``q1140119_bochner_integrable_on
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (normE : 'e -> real) (s : real set) (f : real -> 'e) <=>
      ?g : real -> 'e.
        q1140119_strongly_measurable_on addE negE normE s g /\
        integrable lborel
          (Normal o (\x. if x IN s then normE (g x) else 0)) /\
        (AE x::lborel. x IN s ==> f x = g x)``);

val q1140119_simple_integral_on_def = new_definition (
  "q1140119_simple_integral_on_def",
  ``q1140119_simple_integral_on
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (smulE : complex -> 'e -> 'e)
      (s : real set) (phi : real -> 'e) =
      ITSET
        (\y acc.
          addE
            (smulE
              (complex_of_real
                (real (measure lborel {x | x IN s /\ phi x = y}))) y)
            acc)
        (IMAGE phi s) zeroE``);

val q1140119_bochner_approximates_on_def = new_definition (
  "q1140119_bochner_approximates_on_def",
  ``q1140119_bochner_approximates_on
      (zeroE : 'e) (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : complex -> 'e -> 'e) (normE : 'e -> real)
      (s : real set) (f : real -> 'e)
      (phi : num -> real -> 'e) (ell : 'e) <=>
      ?g : real -> 'e.
        q1140119_strongly_measurable_on addE negE normE s g /\
        integrable lborel
          (Normal o (\x. if x IN s then normE (g x) else 0)) /\
        (AE x::lborel. x IN s ==> f x = g x) /\
        (!n. q1140119_measurable_simple_on s (phi n)) /\
        (!n.
          integrable lborel
            (Normal o (\x. if x IN s then normE (phi n x) else 0))) /\
        (!n.
          integrable lborel
            (Normal o
              (\x.
                if x IN s
                then normE (addE (phi n x) (negE (g x)))
                else 0))) /\
        (((\n.
            real
              (integral lborel
                (Normal o
                  (\x.
                    if x IN s
                    then normE (addE (phi n x) (negE (g x)))
                    else 0)))) -->
          0) sequentially) /\
        q1140119_tendsto addE negE normE
          (\n. q1140119_simple_integral_on zeroE addE smulE s (phi n))
          ell``);

val q1140119_bochner_integral_on_def = new_definition (
  "q1140119_bochner_integral_on_def",
  ``q1140119_bochner_integral_on
      (zeroE : 'e) (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : complex -> 'e -> 'e) (normE : 'e -> real)
      (s : real set) (f : real -> 'e) =
      if q1140119_complete addE negE normE /\
         q1140119_bochner_integrable_on addE negE normE s f
      then
        @ell.
          ?phi : num -> real -> 'e.
            q1140119_bochner_approximates_on
              zeroE addE negE smulE normE s f phi ell
      else
        zeroE``);

val q1140119_interval_integral_def = new_definition (
  "q1140119_interval_integral_def",
  ``q1140119_interval_integral
      (zeroE : 'e) (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : complex -> 'e -> 'e) (normE : 'e -> real)
      (f : real -> 'e) (a : real) (b : real) =
      if a <= b
      then
        q1140119_bochner_integral_on
          zeroE addE negE smulE normE (interval (a,b)) f
      else
        negE
          (q1140119_bochner_integral_on
            zeroE addE negE smulE normE (interval (b,a)) f)``);

val q1140119_rectangle_def = new_definition (
  "q1140119_rectangle_def",
  ``q1140119_rectangle (z : complex) (w : complex) (u : complex) <=>
      ((RE z <= RE u /\ RE u <= RE w) \/
       (RE w <= RE u /\ RE u <= RE z)) /\
      ((IM z <= IM u /\ IM u <= IM w) \/
       (IM w <= IM u /\ IM u <= IM z))``);

val q1140119_wedge_integral_def = new_definition (
  "q1140119_wedge_integral_def",
  ``q1140119_wedge_integral
      (zeroE : 'e) (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : complex -> 'e -> 'e) (normE : 'e -> real)
      (z : complex) (w : complex) (f : complex -> 'e) =
      addE
        (q1140119_interval_integral
          zeroE addE negE smulE normE
          (\x. f (complex_of_real x + complex_of_real (IM z) * i))
          (RE z) (RE w))
        (smulE i
          (q1140119_interval_integral
            zeroE addE negE smulE normE
            (\y. f (complex_of_real (RE w) + complex_of_real y * i))
            (IM z) (IM w)))``);

val q1140119_is_conservative_on_def = new_definition (
  "q1140119_is_conservative_on_def",
  ``q1140119_is_conservative_on
      (zeroE : 'e) (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : complex -> 'e -> 'e) (normE : 'e -> real)
      (f : complex -> 'e) (U : complex set) <=>
      !z w : complex.
        (!u. q1140119_rectangle z w u ==> u IN U) ==>
        q1140119_wedge_integral
          zeroE addE negE smulE normE z w f =
        negE
          (q1140119_wedge_integral
            zeroE addE negE smulE normE w z f)``);

val q1140119_is_open_def = new_definition (
  "q1140119_is_open_def",
  ``q1140119_is_open (U : complex set) <=>
      !x : complex.
        x IN U ==>
        ?radius : real.
          0 < radius /\
          !y : complex. modu (y - x) < radius ==> y IN U``);

val q1140119_continuous_on_def = new_definition (
  "q1140119_continuous_on_def",
  ``q1140119_continuous_on
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (normE : 'e -> real) (f : complex -> 'e) (U : complex set) <=>
      !x : complex.
        x IN U ==>
        !epsilon : real.
          0 < epsilon ==>
          ?delta : real.
            0 < delta /\
            !y : complex.
              y IN U /\ modu (y - x) < delta ==>
              normE (addE (f y) (negE (f x))) < epsilon``);

val q1140119_bounded_complex_linear_def = new_definition (
  "q1140119_bounded_complex_linear_def",
  ``q1140119_bounded_complex_linear
      (addE : 'e -> 'e -> 'e) (smulE : complex -> 'e -> 'e)
      (normE : 'e -> real) (L : complex -> 'e) <=>
      (!z w. L (z + w) = addE (L z) (L w)) /\
      (!a z. L (a * z) = smulE a (L z)) /\
      ?C : real. 0 <= C /\ !z. normE (L z) <= C * modu z``);

val q1140119_differentiable_on_def = new_definition (
  "q1140119_differentiable_on_def",
  ``q1140119_differentiable_on
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : complex -> 'e -> 'e) (normE : 'e -> real)
      (f : complex -> 'e) (U : complex set) <=>
      !x : complex.
        x IN U ==>
        ?L : complex -> 'e.
          q1140119_bounded_complex_linear addE smulE normE L /\
          !epsilon : real.
            0 < epsilon ==>
            ?delta : real.
              0 < delta /\
              !y : complex.
                y IN U /\
                0 < modu (y - x) /\ modu (y - x) < delta
                ==>
                normE
                  (addE
                    (addE (f y) (negE (f x)))
                    (negE (L (y - x)))) <
                epsilon * modu (y - x)``);

val isConservativeOn_and_continuousOn_iff_isDifferentiableOn =
  ``!(zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (smulE : complex -> 'e -> 'e)
      (normE : 'e -> real) (f : complex -> 'e) (U : complex set).
      q1140119_normed_complex_space zeroE addE negE smulE normE /\
      q1140119_complete addE negE normE /\
      q1140119_is_open U
      ==>
      (q1140119_is_conservative_on
          zeroE addE negE smulE normE f U /\
       q1140119_continuous_on addE negE normE f U
       <=>
       q1140119_differentiable_on addE negE smulE normE f U)``;

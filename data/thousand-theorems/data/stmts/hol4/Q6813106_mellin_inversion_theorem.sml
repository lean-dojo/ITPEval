(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q6813106 (thousand-theorems__hol4__Q6813106), "Mellin inversion theorem":
  for a function into a complete complex normed space, Mellin convergence,
  vertical integrability of its transform, and continuity at a positive point
  imply inversion at that point. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory transcTheory complexTheory;
open topologyTheory real_topologyTheory extrealTheory sigma_algebraTheory;
open measureTheory borelTheory lebesgueTheory lebesgue_measureTheory;

val q6813106_complex_normed_space_def = new_definition (
  "q6813106_complex_normed_space_def",
  ``q6813106_complex_normed_space
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : complex -> 'e -> 'e) (norm : 'e -> real) <=>
      (!x y z. add x (add y z) = add (add x y) z) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x. smul 1 x = x) /\
      (!a b x. smul (a * b) x = smul a (smul b x)) /\
      (!a b x. smul (a + b) x = add (smul a x) (smul b x)) /\
      (!a x y. smul a (add x y) = add (smul a x) (smul a y)) /\
      (!x. smul 0 x = zero) /\
      (!a. smul a zero = zero) /\
      (!x. neg x = smul (-1) x) /\
      (!x. 0 <= norm x) /\
      (!x. (norm x = 0) <=> (x = zero)) /\
      (!x. norm (neg x) = norm x) /\
      (!x y. norm (add x y) <= norm x + norm y) /\
      (!a x. norm (smul a x) = modu a * norm x)``);

val q6813106_tendsto_def = new_definition (
  "q6813106_tendsto_def",
  ``q6813106_tendsto
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (u : num -> 'e) (ell : 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num.
          !n : num.
            N <= n ==> norm (add (u n) (neg ell)) < epsilon``);

val q6813106_cauchy_def = new_definition (
  "q6813106_cauchy_def",
  ``q6813106_cauchy
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (u : num -> 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num.
          !p q : num.
            N <= p /\ N <= q ==>
            norm (add (u p) (neg (u q))) < epsilon``);

val q6813106_complete_def = new_definition (
  "q6813106_complete_def",
  ``q6813106_complete
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) <=>
      !u : num -> 'e.
        q6813106_cauchy add neg norm u ==>
        ?ell : 'e. q6813106_tendsto add neg norm u ell``);

val q6813106_measurable_simple_def = new_definition (
  "q6813106_measurable_simple_def",
  ``q6813106_measurable_simple
      (m : 'a m_space) (s : 'a -> 'e) <=>
      FINITE (IMAGE s UNIV) /\
      !y : 'e. {x | s x = y} IN measurable_sets m``);

val q6813106_strongly_measurable_def = new_definition (
  "q6813106_strongly_measurable_def",
  ``q6813106_strongly_measurable
      (m : 'a m_space)
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (f : 'a -> 'e) <=>
      ?s : num -> 'a -> 'e.
        (!n. q6813106_measurable_simple m (s n)) /\
        !x. q6813106_tendsto add neg norm (\n. s n x) (f x)``);

val q6813106_bochner_integrable_def = new_definition (
  "q6813106_bochner_integrable_def",
  ``q6813106_bochner_integrable
      (m : 'a m_space)
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (f : 'a -> 'e) <=>
      ?g : 'a -> 'e.
        q6813106_strongly_measurable m add neg norm g /\
        integrable m (Normal o (\x. norm (g x))) /\
        (AE x::m. f x = g x)``);

val q6813106_simple_integral_def = new_definition (
  "q6813106_simple_integral_def",
  ``q6813106_simple_integral
      (m : 'a m_space)
      (zero : 'e) (add : 'e -> 'e -> 'e)
      (smul : complex -> 'e -> 'e) (s : 'a -> 'e) =
      ITSET
        (\y acc.
          add
            (smul
              (complex_of_real (real (measure m {x | s x = y}))) y)
            acc)
        (IMAGE s UNIV DELETE zero) zero``);

val q6813106_bochner_approximates_def = new_definition (
  "q6813106_bochner_approximates_def",
  ``q6813106_bochner_approximates
      (m : 'a m_space)
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : complex -> 'e -> 'e) (norm : 'e -> real)
      (f : 'a -> 'e) (s : num -> 'a -> 'e) (ell : 'e) <=>
      ?g : 'a -> 'e.
        q6813106_strongly_measurable m add neg norm g /\
        integrable m (Normal o (\x. norm (g x))) /\
        (AE x::m. f x = g x) /\
        (!n. q6813106_measurable_simple m (s n)) /\
        (!n. integrable m (Normal o (\x. norm (s n x)))) /\
        (!n.
          integrable m
            (Normal o (\x. norm (add (s n x) (neg (g x)))))) /\
        (((\n.
            real
              (integral m
                (Normal o
                  (\x. norm (add (s n x) (neg (g x))))))) -->
          0) sequentially) /\
        q6813106_tendsto add neg norm
          (\n. q6813106_simple_integral m zero add smul (s n))
          ell``);

val q6813106_bochner_integral_def = new_definition (
  "q6813106_bochner_integral_def",
  ``q6813106_bochner_integral
      (m : 'a m_space)
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : complex -> 'e -> 'e) (norm : 'e -> real)
      (f : 'a -> 'e) =
      if q6813106_complete add neg norm /\
         q6813106_bochner_integrable m add neg norm f
      then
        @ell : 'e.
          ?s : num -> 'a -> 'e.
            q6813106_bochner_approximates
              m zero add neg smul norm f s ell
      else
        zero``);

val q6813106_principal_arg_def = new_definition (
  "q6813106_principal_arg_def",
  ``q6813106_principal_arg (z : complex) =
      if z = 0 then 0
      else if arg z <= pi then arg z else arg z - 2 * pi``);

val q6813106_complex_log_def = new_definition (
  "q6813106_complex_log_def",
  ``q6813106_complex_log (z : complex) =
      (ln (modu z),q6813106_principal_arg z)``);

val q6813106_complex_cpow_def = new_definition (
  "q6813106_complex_cpow_def",
  ``q6813106_complex_cpow (z : complex) (w : complex) =
      if z = 0 then
        if w = 0 then 1 else 0
      else
        complex_exp (q6813106_complex_log z * w)``);

val q6813106_continuous_at_def = new_definition (
  "q6813106_continuous_at_def",
  ``q6813106_continuous_at
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (f : real -> 'e) (x : real) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?delta : real.
          0 < delta /\
          !y : real.
            abs (y - x) < delta ==>
            norm (add (f y) (neg (f x))) < epsilon``);

val q6813106_mellin_convergent_def = new_definition (
  "q6813106_mellin_convergent_def",
  ``q6813106_mellin_convergent
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : complex -> 'e -> 'e) (norm : 'e -> real)
      (f : real -> 'e) (s : complex) <=>
      q6813106_bochner_integrable lborel add neg norm
        (\t.
          if 0 < t then
            smul
              (q6813106_complex_cpow
                (complex_of_real t) (s - 1))
              (f t)
          else
            zero)``);

val q6813106_mellin_def = new_definition (
  "q6813106_mellin_def",
  ``q6813106_mellin
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : complex -> 'e -> 'e) (norm : 'e -> real)
      (f : real -> 'e) (s : complex) =
      q6813106_bochner_integral
        lborel zero add neg smul norm
        (\t.
          if 0 < t then
            smul
              (q6813106_complex_cpow
                (complex_of_real t) (s - 1))
              (f t)
          else
            zero)``);

val q6813106_vertical_integrable_def = new_definition (
  "q6813106_vertical_integrable_def",
  ``q6813106_vertical_integrable
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (transform : complex -> 'e) (sigma0 : real) <=>
      q6813106_bochner_integrable lborel add neg norm
        (\y.
          transform
            (complex_of_real sigma0 +
             complex_of_real y * i))``);

val q6813106_mellin_inv_def = new_definition (
  "q6813106_mellin_inv_def",
  ``q6813106_mellin_inv
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : complex -> 'e -> 'e) (norm : 'e -> real)
      (sigma0 : real) (transform : complex -> 'e) (x : real) =
      smul
        (complex_of_real (1 / (2 * pi)))
        (q6813106_bochner_integral
          lborel zero add neg smul norm
          (\y.
            let z =
              complex_of_real sigma0 +
              complex_of_real y * i
            in
              smul
                (q6813106_complex_cpow
                  (complex_of_real x) (-z))
                (transform z)))``);

val mellin_inversion =
  ``!(zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : complex -> 'e -> 'e) (norm : 'e -> real)
      (sigma0 : real) (f : real -> 'e) (x : real).
      q6813106_complex_normed_space zero add neg smul norm /\
      q6813106_complete add neg norm /\
      0 < x /\
      q6813106_mellin_convergent
        zero add neg smul norm f (complex_of_real sigma0) /\
      q6813106_vertical_integrable add neg norm
        (q6813106_mellin zero add neg smul norm f) sigma0 /\
      q6813106_continuous_at add neg norm f x
      ==>
      q6813106_mellin_inv
        zero add neg smul norm sigma0
        (q6813106_mellin zero add neg smul norm f) x =
      f x``;

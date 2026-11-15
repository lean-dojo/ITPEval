(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1153584, "Monotone convergence theorem": almost-everywhere monotone
  convergence of nonnegative extended-real functions passes through the lower
  Lebesgue integral, and an integrable antitone real-valued sequence has
  convergent Bochner integrals. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory extrealTheory;
open topologyTheory real_topologyTheory measureTheory borelTheory lebesgueTheory;

val q1153584_ae_measurable_def = new_definition (
  "q1153584_ae_measurable_def",
  ``q1153584_ae_measurable
      (m : 'a m_space) (h : 'a -> extreal) <=>
      ?g : 'a -> extreal.
        g IN measurable (m_space m, measurable_sets m) Borel /\
        (AE x::m. h x = g x)``);

val q1153584_ae_integrable_def = new_definition (
  "q1153584_ae_integrable_def",
  ``q1153584_ae_integrable
      (m : 'a m_space) (h : 'a -> real) <=>
      ?g : 'a -> real.
        integrable m (Normal o g) /\
        (AE x::m. h x = g x)``);

val q1153584_tendsto_ennreal_def = new_definition (
  "q1153584_tendsto_ennreal_def",
  ``q1153584_tendsto_ennreal
      (u : num -> extreal) (ell : extreal) <=>
      (ell = PosInf /\
       !b : real.
         ?N. !n. N <= n ==> Normal b < u n) \/
      (?r : real.
         ell = Normal r /\
         !epsilon : real.
           0 < epsilon ==>
           ?N. !n.
             N <= n ==>
             Normal (r - epsilon) < u n /\
             u n < Normal (r + epsilon))``);

val integral_tendsto_of_tendsto_of_antitone =
  ``!(m : 'a m_space) (f : num -> 'a -> real) (F : 'a -> real).
      measure_space m /\
      m_space m = UNIV /\
      (!n. q1153584_ae_integrable m (f n)) /\
      q1153584_ae_integrable m F /\
      (AE x::m. !i j. i <= j ==> f j x <= f i x) /\
      (AE x::m. ((\n. f n x) --> F x) sequentially)
      ==>
      ((\n. real (integral m (Normal o (f n)))) -->
        real (integral m (Normal o F))) sequentially``;

val lintegral_tendsto_of_tendsto_of_monotone =
  ``!(m : 'a m_space) (f : num -> 'a -> extreal)
      (F : 'a -> extreal).
      measure_space m /\
      m_space m = UNIV /\
      (!n x. 0 <= f n x) /\
      (!x. 0 <= F x) /\
      (!n. q1153584_ae_measurable m (f n)) /\
      (AE x::m. !i j. i <= j ==> f i x <= f j x) /\
      (AE x::m. q1153584_tendsto_ennreal (\n. f n x) (F x))
      ==>
      q1153584_tendsto_ennreal
        (\n. pos_fn_integral m (f n))
        (pos_fn_integral m F)``;

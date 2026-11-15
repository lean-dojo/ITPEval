(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1067156X, "Bounded convergence theorem": uniformly bounded nonnegative
  bounded continuous functions converging almost everywhere along a countably
  generated filter have convergent lower Lebesgue integrals for a finite
  measure; the sequence specialization uses pointwise convergence. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory extrealTheory;
open topologyTheory real_topologyTheory measureTheory borelTheory lebesgueTheory;

val q1067156x_filter_def = new_definition (
  "q1067156x_filter_def",
  ``q1067156x_filter (L : ('i set) set) <=>
      UNIV IN L /\
      (!s t. s IN L /\ s SUBSET t ==> t IN L) /\
      (!s t. s IN L /\ t IN L ==> s INTER t IN L)``);

val q1067156x_countably_generated_def = new_definition (
  "q1067156x_countably_generated_def",
  ``q1067156x_countably_generated (L : ('i set) set) <=>
      ?B : num -> 'i set.
        (!m n. m <= n ==> B n SUBSET B m) /\
        !s. s IN L <=> ?n. B n SUBSET s``);

val q1067156x_eventually_def = new_definition (
  "q1067156x_eventually_def",
  ``q1067156x_eventually (L : ('i set) set) (P : 'i -> bool) <=>
      {i | P i} IN L``);

val q1067156x_at_top_def = new_definition (
  "q1067156x_at_top_def",
  ``q1067156x_at_top (s : num set) <=>
      ?N. !n. N <= n ==> n IN s``);

val q1067156x_tendsto_nnreal_def = new_definition (
  "q1067156x_tendsto_nnreal_def",
  ``q1067156x_tendsto_nnreal
      (L : ('i set) set) (u : 'i -> real) (ell : real) <=>
      !epsilon.
        0 < epsilon ==>
        q1067156x_eventually L
          (\i. abs (u i - ell) < epsilon)``);

val q1067156x_tendsto_ennreal_def = new_definition (
  "q1067156x_tendsto_ennreal_def",
  ``q1067156x_tendsto_ennreal
      (L : ('i set) set) (u : 'i -> extreal) (ell : extreal) <=>
      !epsilon.
        0 < epsilon ==>
        q1067156x_eventually L
          (\i. dist extreal_mr1 (u i,ell) < epsilon)``);

val tendsto_lintegral_nn_filter_of_le_const =
  ``!(m : 'a m_space) (top : 'a topology)
      (L : ('i set) set) (fs : 'i -> 'a -> real)
      (c : real) (f : 'a -> real).
      measure_space m /\
      m_space m = UNIV /\
      measure m UNIV <> PosInf /\
      topspace top = UNIV /\
      (!s. open_in top s ==> s IN measurable_sets m) /\
      q1067156x_filter L /\
      q1067156x_countably_generated L /\
      0 <= c /\
      (!i. fs i IN bounded_continuous top) /\
      (!i x. 0 <= fs i x) /\
      (!x. 0 <= f x) /\
      q1067156x_eventually L
        (\i. almost_everywhere m (\x. fs i x <= c)) /\
      almost_everywhere m
        (\x. q1067156x_tendsto_nnreal L (\i. fs i x) (f x))
      ==>
      q1067156x_tendsto_ennreal L
        (\i. pos_fn_integral m (Normal o (fs i)))
        (pos_fn_integral m (Normal o f))``;

val tendsto_lintegral_nn_of_le_const =
  ``!(m : 'a m_space) (top : 'a topology)
      (fs : num -> 'a -> real) (c : real) (f : 'a -> real).
      measure_space m /\
      m_space m = UNIV /\
      measure m UNIV <> PosInf /\
      topspace top = UNIV /\
      (!s. open_in top s ==> s IN measurable_sets m) /\
      0 <= c /\
      (!n. fs n IN bounded_continuous top) /\
      (!n x. 0 <= fs n x /\ fs n x <= c) /\
      (!x. 0 <= f x) /\
      (!x.
        q1067156x_tendsto_nnreal
          q1067156x_at_top (\n. fs n x) (f x))
      ==>
      q1067156x_tendsto_ennreal q1067156x_at_top
        (\n. pos_fn_integral m (Normal o (fs n)))
        (pos_fn_integral m (Normal o f))``;

(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1191319 (thousand-theorems__hol4__Q1191319), "Radon–Nikodym theorem":
  under a Lebesgue decomposition, absolute continuity is equivalent to
  recovery of the measure from its chosen Radon-Nikodym density. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory extrealTheory;
open sigma_algebraTheory measureTheory borelTheory lebesgueTheory;

val q1191319_mutually_singular_def = new_definition (
  "q1191319_mutually_singular_def",
  ``q1191319_mutually_singular
      (xi : 'a m_space) (nu : 'a m_space) <=>
      ?s.
        s IN measurable_sets nu /\
        measure xi (m_space nu DIFF s) = 0 /\
        measure nu s = 0``);

val q1191319_decomposition_witness_def = new_definition (
  "q1191319_decomposition_witness_def",
  ``q1191319_decomposition_witness
      (mu : 'a m_space) (nu : 'a m_space)
      (xi : 'a m_space) (f : 'a -> extreal) <=>
      measure_space xi /\
      m_space xi = m_space mu /\
      measurable_sets xi = measurable_sets mu /\
      f IN measurable (m_space nu, measurable_sets nu) Borel /\
      (!x. 0 <= f x) /\
      q1191319_mutually_singular xi nu /\
      !s.
        s IN measurable_sets mu ==>
        measure mu s =
          measure xi s + measure (density nu f) s``);

val q1191319_have_lebesgue_decomposition_def = new_definition (
  "q1191319_have_lebesgue_decomposition_def",
  ``q1191319_have_lebesgue_decomposition
      (mu : 'a m_space) (nu : 'a m_space) <=>
      ?xi f. q1191319_decomposition_witness mu nu xi f``);

val q1191319_rn_deriv_def = new_definition (
  "q1191319_rn_deriv_def",
  ``q1191319_rn_deriv
      (mu : 'a m_space) (nu : 'a m_space) =
      if q1191319_have_lebesgue_decomposition mu nu then
        SND
          (@p : 'a m_space # ('a -> extreal).
            q1191319_decomposition_witness mu nu (FST p) (SND p))
      else
        (\x. 0)``);

val absolutely_continuous_iff_density_rn_deriv_eq =
  ``!(mu : 'a m_space) (nu : 'a m_space).
      measure_space mu /\
      measure_space nu /\
      m_space mu = UNIV /\
      m_space nu = UNIV /\
      measurable_sets mu = measurable_sets nu /\
      q1191319_have_lebesgue_decomposition mu nu
      ==>
      (measure_absolutely_continuous (measure mu) nu <=>
       measure_space_eq
         (density nu (q1191319_rn_deriv mu nu))
         mu)``;

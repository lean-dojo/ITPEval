(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q191693, "Lebesgue's decomposition theorem": an s-finite measure admits,
  relative to a sigma-finite measure, a decomposition into a mutually singular
  measure and a measure with a nonnegative measurable density. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory extrealTheory;
open sigma_algebraTheory measureTheory borelTheory lebesgueTheory;

val q191693_sfinite_def = new_definition (
  "q191693_sfinite_def",
  ``q191693_sfinite (mu : 'a m_space) <=>
      ?parts : num -> 'a set -> extreal.
        (!n.
          measure_space
            (m_space mu, measurable_sets mu, parts n) /\
          parts n (m_space mu) <> PosInf) /\
        !s.
          s IN measurable_sets mu ==>
          measure mu s = suminf (\n. parts n s)``);

val q191693_mutually_singular_def = new_definition (
  "q191693_mutually_singular_def",
  ``q191693_mutually_singular
      (xi : 'a m_space) (nu : 'a m_space) <=>
      ?s : 'a set.
        s IN measurable_sets nu /\
        measure xi s = 0 /\
        measure nu (m_space nu DIFF s) = 0``);

val q191693_decomposition_witness_def = new_definition (
  "q191693_decomposition_witness_def",
  ``q191693_decomposition_witness
      (mu : 'a m_space) (nu : 'a m_space)
      (xi : 'a m_space) (f : 'a -> extreal) <=>
      measure_space xi /\
      m_space xi = m_space mu /\
      measurable_sets xi = measurable_sets mu /\
      f IN measurable (m_space nu, measurable_sets nu) Borel /\
      (!x. 0 <= f x) /\
      q191693_mutually_singular xi nu /\
      !s.
        s IN measurable_sets mu ==>
        measure mu s =
          measure xi s + measure (density nu f) s``);

val q191693_have_lebesgue_decomposition_def = new_definition (
  "q191693_have_lebesgue_decomposition_def",
  ``q191693_have_lebesgue_decomposition
      (mu : 'a m_space) (nu : 'a m_space) <=>
      ?xi f. q191693_decomposition_witness mu nu xi f``);

val lebesgue_decomposition_theorem =
  ``!(mu : 'a m_space) (nu : 'a m_space).
      measure_space mu /\
      measure_space nu /\
      m_space mu = UNIV /\
      m_space nu = UNIV /\
      measurable_sets mu = measurable_sets nu /\
      q191693_sfinite mu /\
      sigma_finite nu
      ==>
      q191693_have_lebesgue_decomposition mu nu``;

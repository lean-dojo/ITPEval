(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q182505, "Bayes' theorem": for two measurable events in a finite measure
  space, conditional probability satisfies Bayes' identity. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory extrealTheory measureTheory;

val q182505_ennreal_inv_def = new_definition (
  "q182505_ennreal_inv_def",
  ``q182505_ennreal_inv (x : extreal) =
      if x = 0 then PosInf else inv x``);

val q182505_cond_def = new_definition (
  "q182505_cond_def",
  ``q182505_cond
      (m : 'a m_space) (event : 'a set) (given : 'a set) =
      q182505_ennreal_inv (measure m given) *
        measure m (given INTER event)``);

val bayes_theorem =
  ``!(m : 'a m_space) (s : 'a set) (t : 'a set).
      finite_measure_space m /\
      m_space m = UNIV /\
      s IN measurable_sets m /\
      t IN measurable_sets m
      ==>
      q182505_cond m t s =
        q182505_ennreal_inv (measure m s) *
          q182505_cond m s t *
          measure m t``;

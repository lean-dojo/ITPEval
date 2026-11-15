(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q5165492, "Continuous mapping theorem": convergence in distribution along
  an arbitrary filter is preserved by composition with a continuous map into
  a Borel measurable topological space. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory extrealTheory;
open topologyTheory real_topologyTheory sigma_algebraTheory measureTheory;
open borelTheory lebesgueTheory probabilityTheory;

val q5165492_filter_def = new_definition (
  "q5165492_filter_def",
  ``q5165492_filter (L : ('i set) set) <=>
      UNIV IN L /\
      (!s t. s IN L /\ s SUBSET t ==> t IN L) /\
      (!s t. s IN L /\ t IN L ==> s INTER t IN L)``);

val q5165492_opens_measurable_def = new_definition (
  "q5165492_opens_measurable_def",
  ``q5165492_opens_measurable
      (top : 'a topology) (a : 'a algebra) <=>
      topspace top = UNIV /\
      sigma_algebra a /\
      space a = UNIV /\
      (!s. open_in top s ==> s IN subsets a)``);

val q5165492_borel_space_def = new_definition (
  "q5165492_borel_space_def",
  ``q5165492_borel_space
      (top : 'a topology) (a : 'a algebra) <=>
      topspace top = UNIV /\
      a = general_borel top``);

val q5165492_ae_measurable_def = new_definition (
  "q5165492_ae_measurable_def",
  ``q5165492_ae_measurable
      (m : 'a m_space) (a : 'b algebra) (f : 'a -> 'b) <=>
      ?h.
        h IN measurable (m_space m,measurable_sets m) a /\
        almost_everywhere m (\x. f x = h x)``);

val q5165492_measurable_rep_def = new_definition (
  "q5165492_measurable_rep_def",
  ``q5165492_measurable_rep
      (m : 'a m_space) (a : 'b algebra) (f : 'a -> 'b) =
      @h.
        h IN measurable (m_space m,measurable_sets m) a /\
        almost_everywhere m (\x. f x = h x)``);

val q5165492_law_def = new_definition (
  "q5165492_law_def",
  ``q5165492_law
      (m : 'a m_space) (a : 'b algebra) (f : 'a -> 'b) =
      (space a,subsets a,distr m (q5165492_measurable_rep m a f))``);

val q5165492_weak_tendsto_def = new_definition (
  "q5165492_weak_tendsto_def",
  ``q5165492_weak_tendsto
      (top : 'a topology) (L : ('i set) set)
      (nu : 'i -> 'a m_space) (nu0 : 'a m_space) <=>
      !f.
        f IN bounded_continuous top ==>
        !epsilon.
          0 < epsilon ==>
          {i |
            dist extreal_mr1
              (integral (nu i) (Normal o f),
               integral nu0 (Normal o f)) < epsilon} IN L``);

val q5165492_tendsto_in_distribution_def = new_definition (
  "q5165492_tendsto_in_distribution_def",
  ``q5165492_tendsto_in_distribution
      (top : 'e topology) (a : 'e algebra) (L : ('i set) set)
      (mu : 'i -> 'w m_space) (mu0 : 'w0 m_space)
      (X : 'i -> 'w -> 'e) (Z : 'w0 -> 'e) <=>
      (!i. q5165492_ae_measurable (mu i) a (X i)) /\
      q5165492_ae_measurable mu0 a Z /\
      q5165492_weak_tendsto top L
        (\i. q5165492_law (mu i) a (X i))
        (q5165492_law mu0 a Z)``);

val continuous_mapping_theorem =
  ``!(topE : 'e topology) (measE : 'e algebra)
      (topF : 'f topology) (measF : 'f algebra)
      (L : ('i set) set)
      (mu : 'i -> 'w m_space) (mu0 : 'w0 m_space)
      (X : 'i -> 'w -> 'e) (Z : 'w0 -> 'e) (g : 'e -> 'f).
      q5165492_opens_measurable topE measE /\
      q5165492_borel_space topF measF /\
      q5165492_filter L /\
      (!i. prob_space (mu i)) /\
      prob_space mu0 /\
      continuous_map (topE,topF) g /\
      q5165492_tendsto_in_distribution
        topE measE L mu mu0 X Z
      ==>
      q5165492_tendsto_in_distribution
        topF measF L mu mu0 (\i. g o X i) (g o Z)``;

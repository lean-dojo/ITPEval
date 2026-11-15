(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q190391 (thousand-theorems__hol4__Q190391), "Central limit theorem":
  independent identically distributed square-integrable real random variables,
  centered and normalized by the square root of the sample size, converge in
  distribution to the Gaussian law with their common variance. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory iterateTheory realTheory transcTheory;
open topologyTheory real_topologyTheory extrealTheory measureTheory borelTheory;
open lebesgueTheory lebesgue_measureTheory probabilityTheory;

val q190391_ae_measurable_def = new_definition (
  "q190391_ae_measurable_def",
  ``q190391_ae_measurable (p : 'a p_space) (X : 'a -> real) <=>
      ?X' : 'a -> real.
        random_variable X' p borel /\
        (AE w::p. X w = X' w)``);

val q190391_representative_def = new_definition (
  "q190391_representative_def",
  ``q190391_representative (p : 'a p_space) (X : 'a -> real) =
      @X' : 'a -> real.
        random_variable X' p borel /\
        (AE w::p. X w = X' w)``);

val q190391_mem_lp_two_def = new_definition (
  "q190391_mem_lp_two_def",
  ``q190391_mem_lp_two (p : 'a p_space) (X : 'a -> real) <=>
      q190391_ae_measurable p X /\
      integrable p
        (\w. Normal ((q190391_representative p X w) pow 2))``);

val q190391_independent_def = new_definition (
  "q190391_independent_def",
  ``q190391_independent
      (p : 'a p_space) (X : num -> 'a -> real) <=>
      ?X' : num -> 'a -> real.
        (!i.
          random_variable (X' i) p borel /\
          (AE w::p. X i w = X' i w)) /\
        indep_vars p X' (\i. borel) UNIV``);

val q190391_has_law_def = new_definition (
  "q190391_has_law_def",
  ``q190391_has_law
      (p : 'a p_space) (X : 'a -> real) (law : real measure) <=>
      ?X' : 'a -> real.
        random_variable X' p borel /\
        (AE w::p. X w = X' w) /\
        !s. s IN subsets borel ==> distribution p X' s = law s``);

val q190391_ident_distrib_def = new_definition (
  "q190391_ident_distrib_def",
  ``q190391_ident_distrib
      (p : 'a p_space) (X : 'a -> real) (Y : 'a -> real) <=>
      ?law : real measure.
        q190391_has_law p X law /\
        q190391_has_law p Y law``);

val q190391_mean_def = new_definition (
  "q190391_mean_def",
  ``q190391_mean (p : 'a p_space) (X : 'a -> real) =
      real
        (integral p
          (Normal o q190391_representative p X))``);

val q190391_variance_def = new_definition (
  "q190391_variance_def",
  ``q190391_variance (p : 'a p_space) (X : 'a -> real) =
      real
        (integral p
          (\w.
            Normal
              ((q190391_representative p X w -
                q190391_mean p X) pow 2)))``);

val q190391_gaussian_law_def = new_definition (
  "q190391_gaussian_law_def",
  ``q190391_gaussian_law (v : real) : real measure =
      if v <= 0 then
        (\s. if s IN subsets borel /\ (0 : real) IN s then 1 else 0)
      else
        density_measure lborel
          (Normal o
            (\x.
              (1 / sqrt (2 * pi * v)) *
              exp (-((x pow 2) / (2 * v)))))``);

val q190391_tendsto_in_distribution_def = new_definition (
  "q190391_tendsto_in_distribution_def",
  ``q190391_tendsto_in_distribution
      (p : 'a p_space) (p' : 'b p_space)
      (Zs : num -> 'a -> real) (Y : 'b -> real) <=>
      ?laws : num -> real measure.
      ?target_law : real measure.
        (!n. q190391_has_law p (Zs n) (laws n)) /\
        q190391_has_law p' Y target_law /\
        !f. f IN bounded_continuous euclidean ==>
          (((\n.
              integral
                (space borel, subsets borel, laws n)
                (Normal o f)) -->
            integral
              (space borel, subsets borel, target_law)
              (Normal o f))
           sequentially)``);

val central_limit_theorem =
  ``!(p : 'a p_space) (p' : 'b p_space)
      (X : num -> 'a -> real) (Y : 'b -> real).
      prob_space p /\
      prob_space p' /\
      q190391_has_law p' Y
        (q190391_gaussian_law (q190391_variance p (X 0))) /\
      q190391_mem_lp_two p (X 0) /\
      q190391_independent p X /\
      (!i. q190391_ident_distrib p (X i) (X 0))
      ==>
      q190391_tendsto_in_distribution p p'
        (\n w.
          inv (sqrt (&n)) *
          (SIGMA (\k. X k w) (count n) -
           &n * q190391_mean p (X 0)))
        Y``;

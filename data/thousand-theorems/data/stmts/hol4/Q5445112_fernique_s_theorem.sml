(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q5445112 (thousand-theorems__hol4__Q5445112), "Fernique's theorem":
  a Gaussian measure on a complete second-countable real normed vector space
  has an integrable positive exponential of the squared norm. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory transcTheory extrealTheory;
open topologyTheory real_topologyTheory sigma_algebraTheory measureTheory;
open borelTheory lebesgueTheory lebesgue_measureTheory;

val q5445112_real_normed_space_def = new_definition (
  "q5445112_real_normed_space_def",
  ``q5445112_real_normed_space
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (norm : 'e -> real) <=>
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

val q5445112_tendsto_def = new_definition (
  "q5445112_tendsto_def",
  ``q5445112_tendsto
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (u : num -> 'e) (x : 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !n : num.
          N <= n ==> norm (add (u n) (neg x)) < epsilon``);

val q5445112_cauchy_def = new_definition (
  "q5445112_cauchy_def",
  ``q5445112_cauchy
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (u : num -> 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !m n : num.
          N <= m /\ N <= n ==>
          norm (add (u m) (neg (u n))) < epsilon``);

val q5445112_complete_def = new_definition (
  "q5445112_complete_def",
  ``q5445112_complete
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) <=>
      !u : num -> 'e.
        q5445112_cauchy add neg norm u ==>
        ?x : 'e. q5445112_tendsto add neg norm u x``);

val q5445112_norm_open_def = new_definition (
  "q5445112_norm_open_def",
  ``q5445112_norm_open
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (u : 'e set) <=>
      !x.
        x IN u ==>
        ?epsilon : real.
          0 < epsilon /\
          !y.
            norm (add y (neg x)) < epsilon ==>
            y IN u``);

val q5445112_norm_topology_def = new_definition (
  "q5445112_norm_topology_def",
  ``q5445112_norm_topology
      (top : 'e topology)
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) <=>
      topspace top = UNIV /\
      !u. open_in top u <=> q5445112_norm_open add neg norm u``);

val q5445112_second_countable_def = new_definition (
  "q5445112_second_countable_def",
  ``q5445112_second_countable (top : 'e topology) <=>
      ?basis : ('e set) set.
        COUNTABLE basis /\
        (!v. v IN basis ==> open_in top v) /\
        !u x.
          open_in top u /\ x IN u ==>
          ?v. v IN basis /\ x IN v /\ v SUBSET u``);

val q5445112_borel_measure_def = new_definition (
  "q5445112_borel_measure_def",
  ``q5445112_borel_measure
      (top : 'e topology) (m : 'e m_space) <=>
      measure_space m /\
      m_space m = UNIV /\
      measurable_sets m = subsets (general_borel top)``);

val q5445112_continuous_linear_functional_def = new_definition (
  "q5445112_continuous_linear_functional_def",
  ``q5445112_continuous_linear_functional
      (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e)
      (norm : 'e -> real) (L : 'e -> real) <=>
      (!x y. L (add x y) = L x + L y) /\
      (!a x. L (smul a x) = a * L x) /\
      ?K : real.
        0 <= K /\
        !x. abs (L x) <= K * norm x``);

val q5445112_gaussian_real_measure_def = new_definition (
  "q5445112_gaussian_real_measure_def",
  ``q5445112_gaussian_real_measure
      (mean : real) (variance : real) (s : real set) =
      if variance = 0 then
        if mean IN s then (1 : extreal) else 0
      else
        density_measure lborel
          (Normal o
            (\x.
              (1 / sqrt (2 * pi * variance)) *
              exp (-((x - mean) pow 2) / (2 * variance))))
          s``);

val q5445112_is_gaussian_def = new_definition (
  "q5445112_is_gaussian_def",
  ``q5445112_is_gaussian
      (m : 'e m_space)
      (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e)
      (norm : 'e -> real) <=>
      !L : 'e -> real.
        q5445112_continuous_linear_functional add smul norm L ==>
        ?mean variance : real.
          0 <= variance /\
          !s : real set.
            s IN subsets borel ==>
            measure m (PREIMAGE L s) =
              q5445112_gaussian_real_measure mean variance s``);

val exists_integrable_exp_sq =
  ``!(top : 'e topology)
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (norm : 'e -> real)
      (m : 'e m_space).
      q5445112_real_normed_space zero add neg smul norm /\
      q5445112_norm_topology top add neg norm /\
      q5445112_second_countable top /\
      q5445112_complete add neg norm /\
      q5445112_borel_measure top m /\
      q5445112_is_gaussian m add smul norm
      ==>
      ?C : real.
        0 < C /\
        integrable m
          (Normal o (\x. exp (C * norm x pow 2)))``;

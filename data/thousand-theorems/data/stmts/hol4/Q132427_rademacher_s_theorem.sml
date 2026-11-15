(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q132427 (thousand-theorems__hol4__Q132427), "Rademacher's theorem": a
  Lipschitz map between finite-dimensional real normed vector spaces is
  differentiable within a measurable set almost everywhere on that set.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory realTheory extrealTheory;
open sigma_algebraTheory measureTheory;

val q132427_real_normed_space_def = new_definition (
  "q132427_real_normed_space_def",
  ``q132427_real_normed_space
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

val q132427_lincomb_def = new_definition (
  "q132427_lincomb_def",
  ``q132427_lincomb
      (zero : 'e) (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e)
      (basis : 'e list) (coeff : num -> real) =
      FOLDL
        (\acc i. add acc (smul (coeff i) (EL i basis)))
        zero
        (GENLIST (\i. i) (LENGTH basis))``);

val q132427_basis_def = new_definition (
  "q132427_basis_def",
  ``q132427_basis
      (zero : 'e) (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e)
      (basis : 'e list) <=>
      ALL_DISTINCT basis /\
      (!coeff : num -> real.
        q132427_lincomb zero add smul basis coeff = zero ==>
        !i. i < LENGTH basis ==> coeff i = 0) /\
      (!x : 'e.
        ?coeff : num -> real.
          q132427_lincomb zero add smul basis coeff = x)``);

val q132427_finite_dimensional_def = new_definition (
  "q132427_finite_dimensional_def",
  ``q132427_finite_dimensional
      (zero : 'e) (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e) <=>
      ?basis : 'e list. q132427_basis zero add smul basis``);

val q132427_open_def = new_definition (
  "q132427_open_def",
  ``q132427_open
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (u : 'e set) <=>
      !x. x IN u ==>
        ?epsilon : real.
          0 < epsilon /\
          !y. norm (add y (neg x)) < epsilon ==> y IN u``);

val q132427_compact_def = new_definition (
  "q132427_compact_def",
  ``q132427_compact
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (k : 'e set) <=>
      !u : num -> 'e.
        (!n. u n IN k) ==>
        ?r : num -> num. ?x : 'e.
          x IN k /\
          (!p q. p < q ==> r p < r q) /\
          !epsilon : real.
            0 < epsilon ==>
            ?N : num. !n : num.
              N <= n ==>
              norm (add (u (r n)) (neg x)) < epsilon``);

val q132427_borel_measure_def = new_definition (
  "q132427_borel_measure_def",
  ``q132427_borel_measure
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (m : 'e m_space) <=>
      measure_space m /\
      m_space m = UNIV /\
      measurable_sets m =
        subsets
          (sigma UNIV
            {u : 'e set | q132427_open add neg norm u})``);

val q132427_translate_def = new_definition (
  "q132427_translate_def",
  ``q132427_translate
      (add : 'e -> 'e -> 'e) (a : 'e) (s : 'e set) =
      {x | ?y. y IN s /\ x = add a y}``);

val q132427_outer_measure_def = new_definition (
  "q132427_outer_measure_def",
  ``q132427_outer_measure (m : 'e m_space) (s : 'e set) =
      inf
        {r : extreal |
          ?t : 'e set.
            s SUBSET t /\
            t IN measurable_sets m /\
            measure m t = r}``);

val q132427_add_haar_measure_def = new_definition (
  "q132427_add_haar_measure_def",
  ``q132427_add_haar_measure
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (m : 'e m_space) <=>
      (!a : 'e. !s : 'e set.
        q132427_outer_measure m (q132427_translate add a s) =
        q132427_outer_measure m s) /\
      (!k : 'e set.
        q132427_compact add neg norm k ==>
        q132427_outer_measure m k <> PosInf) /\
      (!u : 'e set.
        q132427_open add neg norm u /\ u <> {} ==>
        q132427_outer_measure m u <> 0)``);

val q132427_continuous_linear_map_def = new_definition (
  "q132427_continuous_linear_map_def",
  ``q132427_continuous_linear_map
      (add_e : 'e -> 'e -> 'e) (smul_e : real -> 'e -> 'e)
      (norm_e : 'e -> real)
      (add_f : 'f -> 'f -> 'f) (smul_f : real -> 'f -> 'f)
      (norm_f : 'f -> real) (L : 'e -> 'f) <=>
      (!x y. L (add_e x y) = add_f (L x) (L y)) /\
      (!a x. L (smul_e a x) = smul_f a (L x)) /\
      ?K : real.
        0 <= K /\
        !x. norm_f (L x) <= K * norm_e x``);

val q132427_lipschitz_on_with_def = new_definition (
  "q132427_lipschitz_on_with_def",
  ``q132427_lipschitz_on_with
      (add_e : 'e -> 'e -> 'e) (neg_e : 'e -> 'e)
      (norm_e : 'e -> real)
      (add_f : 'f -> 'f -> 'f) (neg_f : 'f -> 'f)
      (norm_f : 'f -> real)
      (C : real) (f : 'e -> 'f) (s : 'e set) <=>
      !x y.
        x IN s /\ y IN s ==>
        norm_f (add_f (f x) (neg_f (f y))) <=
          C * norm_e (add_e x (neg_e y))``);

val q132427_has_fderiv_within_at_def = new_definition (
  "q132427_has_fderiv_within_at_def",
  ``q132427_has_fderiv_within_at
      (add_e : 'e -> 'e -> 'e) (neg_e : 'e -> 'e)
      (smul_e : real -> 'e -> 'e) (norm_e : 'e -> real)
      (add_f : 'f -> 'f -> 'f) (neg_f : 'f -> 'f)
      (smul_f : real -> 'f -> 'f) (norm_f : 'f -> real)
      (f : 'e -> 'f) (L : 'e -> 'f) (s : 'e set) (x : 'e) <=>
      q132427_continuous_linear_map
        add_e smul_e norm_e add_f smul_f norm_f L /\
      !epsilon : real.
        0 < epsilon ==>
        ?delta : real.
          0 < delta /\
          !y.
            y IN s /\
            norm_e (add_e y (neg_e x)) < delta ==>
            norm_f
              (add_f
                (add_f (f y) (neg_f (f x)))
                (neg_f (L (add_e y (neg_e x))))) <=
            epsilon * norm_e (add_e y (neg_e x))``);

val q132427_differentiable_within_at_def = new_definition (
  "q132427_differentiable_within_at_def",
  ``q132427_differentiable_within_at
      (add_e : 'e -> 'e -> 'e) (neg_e : 'e -> 'e)
      (smul_e : real -> 'e -> 'e) (norm_e : 'e -> real)
      (add_f : 'f -> 'f -> 'f) (neg_f : 'f -> 'f)
      (smul_f : real -> 'f -> 'f) (norm_f : 'f -> real)
      (f : 'e -> 'f) (s : 'e set) (x : 'e) <=>
      ?L : 'e -> 'f.
        q132427_has_fderiv_within_at
          add_e neg_e smul_e norm_e
          add_f neg_f smul_f norm_f f L s x``);

val LipschitzOnWith_ae_differentiableWithinAt =
  ``!(zero_e : 'e) (add_e : 'e -> 'e -> 'e) (neg_e : 'e -> 'e)
      (smul_e : real -> 'e -> 'e) (norm_e : 'e -> real)
      (zero_f : 'f) (add_f : 'f -> 'f -> 'f) (neg_f : 'f -> 'f)
      (smul_f : real -> 'f -> 'f) (norm_f : 'f -> real)
      (m : 'e m_space) (C : real) (f : 'e -> 'f) (s : 'e set).
      q132427_real_normed_space zero_e add_e neg_e smul_e norm_e /\
      q132427_real_normed_space zero_f add_f neg_f smul_f norm_f /\
      q132427_finite_dimensional zero_e add_e smul_e /\
      q132427_finite_dimensional zero_f add_f smul_f /\
      q132427_borel_measure add_e neg_e norm_e m /\
      q132427_add_haar_measure add_e neg_e norm_e m /\
      0 <= C /\
      q132427_lipschitz_on_with
        add_e neg_e norm_e add_f neg_f norm_f C f s /\
      s IN measurable_sets m
      ==>
      almost_everywhere m (\x.
        x IN s ==>
        q132427_differentiable_within_at
          add_e neg_e smul_e norm_e
          add_f neg_f smul_f norm_f f s x)``;

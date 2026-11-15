(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q530152 (thousand-theorems__hol4__Q530152), "Picard-Lindelöf theorem": a
  time-dependent vector field on a real Banach space satisfying local
  Lipschitz, continuity, norm-bound, and interval-size conditions has a local
  solution through each permitted initial point. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val q530152_real_normed_space_def = new_definition (
  "q530152_real_normed_space_def",
  ``q530152_real_normed_space
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
      (!x. (norm x = 0) <=> (x = zero)) /\
      (!x y. norm (add x y) <= norm x + norm y) /\
      (!a x. norm (smul a x) = abs a * norm x)``);

val q530152_tendsto_sequence_def = new_definition (
  "q530152_tendsto_sequence_def",
  ``q530152_tendsto_sequence
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e) (norm : 'e -> real)
      (u : num -> 'e) (ell : 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num.
          !n : num.
            N <= n ==>
            norm (add (u n) (neg ell)) < epsilon``);

val q530152_cauchy_sequence_def = new_definition (
  "q530152_cauchy_sequence_def",
  ``q530152_cauchy_sequence
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e) (norm : 'e -> real)
      (u : num -> 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num.
          !m n : num.
            N <= m /\ N <= n ==>
            norm (add (u m) (neg (u n))) < epsilon``);

val q530152_complete_space_def = new_definition (
  "q530152_complete_space_def",
  ``q530152_complete_space
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e) (norm : 'e -> real) <=>
      !u : num -> 'e.
        q530152_cauchy_sequence add neg norm u ==>
        ?ell : 'e.
          q530152_tendsto_sequence add neg norm u ell``);

val q530152_mem_Icc_def = new_definition (
  "q530152_mem_Icc_def",
  ``q530152_mem_Icc (tmin : real) (tmax : real) (t : real) <=>
      tmin <= t /\ t <= tmax``);

val q530152_mem_closed_ball_def = new_definition (
  "q530152_mem_closed_ball_def",
  ``q530152_mem_closed_ball
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e) (norm : 'e -> real)
      (center : 'e) (radius : real) (x : 'e) <=>
      norm (add x (neg center)) <= radius``);

val q530152_lipschitz_on_with_def = new_definition (
  "q530152_lipschitz_on_with_def",
  ``q530152_lipschitz_on_with
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e) (norm : 'e -> real)
      (k : real) (g : 'e -> 'e) (center : 'e) (radius : real) <=>
      !x y.
        q530152_mem_closed_ball add neg norm center radius x /\
        q530152_mem_closed_ball add neg norm center radius y
        ==>
        norm (add (g x) (neg (g y))) <=
          k * norm (add x (neg y))``);

val q530152_continuous_on_Icc_def = new_definition (
  "q530152_continuous_on_Icc_def",
  ``q530152_continuous_on_Icc
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e) (norm : 'e -> real)
      (g : real -> 'e) (tmin : real) (tmax : real) <=>
      !t.
        q530152_mem_Icc tmin tmax t ==>
        !epsilon : real.
          0 < epsilon ==>
          ?delta : real.
            0 < delta /\
            !s.
              q530152_mem_Icc tmin tmax s /\
              abs (s - t) < delta
              ==>
              norm (add (g s) (neg (g t))) < epsilon``);

val q530152_real_max_def = new_definition (
  "q530152_real_max_def",
  ``q530152_real_max (x : real) (y : real) =
      if x <= y then y else x``);

val q530152_is_picard_lindelof_def = new_definition (
  "q530152_is_picard_lindelof_def",
  ``q530152_is_picard_lindelof
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e) (norm : 'e -> real)
      (f : real -> 'e -> 'e)
      (tmin : real) (tmax : real) (t0 : real) (x0 : 'e)
      (a : real) (r : real) (ell : real) (k : real) <=>
      (!t.
        q530152_mem_Icc tmin tmax t ==>
        q530152_lipschitz_on_with add neg norm k (f t) x0 a) /\
      (!x.
        q530152_mem_closed_ball add neg norm x0 a x ==>
        q530152_continuous_on_Icc
          add neg norm (\t. f t x) tmin tmax) /\
      (!t x.
        q530152_mem_Icc tmin tmax t /\
        q530152_mem_closed_ball add neg norm x0 a x
        ==>
        norm (f t x) <= ell) /\
      ell * q530152_real_max (tmax - t0) (t0 - tmin) <= a - r``);

val q530152_has_deriv_within_at_def = new_definition (
  "q530152_has_deriv_within_at_def",
  ``q530152_has_deriv_within_at
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (norm : 'e -> real)
      (alpha : real -> 'e) (v : 'e)
      (tmin : real) (tmax : real) (t : real) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?delta : real.
          0 < delta /\
          !s.
            q530152_mem_Icc tmin tmax s /\
            0 < abs (s - t) /\
            abs (s - t) < delta
            ==>
            norm
              (add
                (add (alpha s) (neg (alpha t)))
                (neg (smul (s - t) v))) <=
              epsilon * abs (s - t)``);

val IsPicardLindelof_exists_eq_forall_mem_Icc_hasDerivWithinAt =
  ``!(zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (norm : 'e -> real)
      (f : real -> 'e -> 'e)
      (tmin : real) (tmax : real) (t0 : real)
      (x0 : 'e) (x : 'e)
      (a : real) (r : real) (ell : real) (k : real).
      q530152_real_normed_space zero add neg smul norm /\
      q530152_complete_space add neg norm /\
      0 <= a /\ 0 <= r /\ 0 <= ell /\ 0 <= k /\
      q530152_mem_Icc tmin tmax t0 /\
      q530152_is_picard_lindelof
        add neg norm f tmin tmax t0 x0 a r ell k /\
      q530152_mem_closed_ball add neg norm x0 r x
      ==>
      ?alpha : real -> 'e.
        alpha t0 = x /\
        !t.
          q530152_mem_Icc tmin tmax t ==>
          q530152_has_deriv_within_at
            add neg smul norm alpha (f t (alpha t))
            tmin tmax t``;

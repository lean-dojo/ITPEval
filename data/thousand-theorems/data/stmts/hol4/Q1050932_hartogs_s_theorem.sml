(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1050932, "Hartogs's theorem": for a function from an open subset of
  the complex plane squared to a complete second-countable complex normed
  space, separate analyticity in each coordinate implies joint analyticity.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory cardinalTheory realTheory;
open complexTheory;

val q1050932_normed_complex_space_def = new_definition (
  "q1050932_normed_complex_space_def",
  ``q1050932_normed_complex_space
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (smulE : complex -> 'e -> 'e)
      (normE : 'e -> real) <=>
      (!x y z. addE (addE x y) z = addE x (addE y z)) /\
      (!x y. addE x y = addE y x) /\
      (!x. addE zeroE x = x) /\
      (!x. addE (negE x) x = zeroE) /\
      (!x. smulE 1 x = x) /\
      (!a b x. smulE (a * b) x = smulE a (smulE b x)) /\
      (!a b x. smulE (a + b) x = addE (smulE a x) (smulE b x)) /\
      (!a x y. smulE a (addE x y) = addE (smulE a x) (smulE a y)) /\
      (!x. smulE 0 x = zeroE) /\
      (!a. smulE a zeroE = zeroE) /\
      (!x. negE x = smulE (-1) x) /\
      (!x. 0 <= normE x) /\
      (!x. (normE x = 0) <=> (x = zeroE)) /\
      (!x y. normE (addE x y) <= normE x + normE y) /\
      (!a x. normE (smulE a x) = modu a * normE x)``);

val q1050932_tendsto_def = new_definition (
  "q1050932_tendsto_def",
  ``q1050932_tendsto
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (normE : 'e -> real) (u : num -> 'e) (x : 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !n : num.
          N <= n ==>
          normE (addE (u n) (negE x)) < epsilon``);

val q1050932_cauchy_def = new_definition (
  "q1050932_cauchy_def",
  ``q1050932_cauchy
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (normE : 'e -> real) (u : num -> 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !m n : num.
          N <= m /\ N <= n ==>
          normE (addE (u m) (negE (u n))) < epsilon``);

val q1050932_complete_def = new_definition (
  "q1050932_complete_def",
  ``q1050932_complete
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (normE : 'e -> real) <=>
      !u : num -> 'e.
        q1050932_cauchy addE negE normE u ==>
        ?x : 'e. q1050932_tendsto addE negE normE u x``);

val q1050932_norm_open_def = new_definition (
  "q1050932_norm_open_def",
  ``q1050932_norm_open
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (normE : 'e -> real) (u : 'e set) <=>
      !x : 'e.
        x IN u ==>
        ?radius : real.
          0 < radius /\
          !y : 'e.
            normE (addE y (negE x)) < radius ==>
            y IN u``);

val q1050932_second_countable_def = new_definition (
  "q1050932_second_countable_def",
  ``q1050932_second_countable
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (normE : 'e -> real) <=>
      ?basis : ('e set) set.
        COUNTABLE basis /\
        (!v. v IN basis ==> q1050932_norm_open addE negE normE v) /\
        !u x.
          q1050932_norm_open addE negE normE u /\ x IN u ==>
          ?v.
            v IN basis /\
            x IN v /\
            v SUBSET u``);

val q1050932_pair_norm_def = new_definition (
  "q1050932_pair_norm_def",
  ``q1050932_pair_norm (z : complex # complex) =
      max (modu (FST z)) (modu (SND z))``);

val q1050932_pair_add_def = new_definition (
  "q1050932_pair_add_def",
  ``q1050932_pair_add
      (z : complex # complex) (w : complex # complex) =
      (FST z + FST w, SND z + SND w)``);

val q1050932_pair_sub_def = new_definition (
  "q1050932_pair_sub_def",
  ``q1050932_pair_sub
      (z : complex # complex) (w : complex # complex) =
      (FST z - FST w, SND z - SND w)``);

val q1050932_open_in_pair_def = new_definition (
  "q1050932_open_in_pair_def",
  ``q1050932_open_in_pair (s : (complex # complex) set) <=>
      !x : complex # complex.
        x IN s ==>
        ?radius : real.
          0 < radius /\
          !y : complex # complex.
            q1050932_pair_norm (q1050932_pair_sub y x) < radius ==>
            y IN s``);

val q1050932_bounded_complex_linear_one_def = new_definition (
  "q1050932_bounded_complex_linear_one_def",
  ``q1050932_bounded_complex_linear_one
      (addE : 'e -> 'e -> 'e) (smulE : complex -> 'e -> 'e)
      (normE : 'e -> real) (L : complex -> 'e) <=>
      (!z w. L (z + w) = addE (L z) (L w)) /\
      (!a z. L (a * z) = smulE a (L z)) /\
      ?C : real.
        0 <= C /\ !z. normE (L z) <= C * modu z``);

val q1050932_complex_frechet_differentiable_one_at_def =
  new_definition (
    "q1050932_complex_frechet_differentiable_one_at_def",
    ``q1050932_complex_frechet_differentiable_one_at
        (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
        (smulE : complex -> 'e -> 'e) (normE : 'e -> real)
        (g : complex -> 'e) (x : complex) <=>
        ?L : complex -> 'e.
          q1050932_bounded_complex_linear_one addE smulE normE L /\
          !epsilon : real.
            0 < epsilon ==>
            ?delta : real.
              0 < delta /\
              !h : complex.
                0 < modu h /\ modu h < delta
                ==>
                normE
                  (addE
                    (addE (g (x + h)) (negE (g x)))
                    (negE (L h))) <
                epsilon * modu h``);

val q1050932_analytic_one_at_def = new_definition (
  "q1050932_analytic_one_at_def",
  ``q1050932_analytic_one_at
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : complex -> 'e -> 'e) (normE : 'e -> real)
      (g : complex -> 'e) (x : complex) <=>
      ?radius : real.
        0 < radius /\
        !y : complex.
          modu (y - x) < radius ==>
          q1050932_complex_frechet_differentiable_one_at
            addE negE smulE normE g y``);

val q1050932_pair_smul_def = new_definition (
  "q1050932_pair_smul_def",
  ``q1050932_pair_smul
      (a : complex) (z : complex # complex) =
      (a * FST z, a * SND z)``);

val q1050932_bounded_complex_linear_pair_def = new_definition (
  "q1050932_bounded_complex_linear_pair_def",
  ``q1050932_bounded_complex_linear_pair
      (addE : 'e -> 'e -> 'e) (smulE : complex -> 'e -> 'e)
      (normE : 'e -> real) (L : complex # complex -> 'e) <=>
      (!z w.
        L (q1050932_pair_add z w) = addE (L z) (L w)) /\
      (!a z.
        L (q1050932_pair_smul a z) = smulE a (L z)) /\
      ?C : real.
        0 <= C /\
        !z. normE (L z) <= C * q1050932_pair_norm z``);

val q1050932_complex_frechet_differentiable_pair_at_def =
  new_definition (
    "q1050932_complex_frechet_differentiable_pair_at_def",
    ``q1050932_complex_frechet_differentiable_pair_at
        (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
        (smulE : complex -> 'e -> 'e) (normE : 'e -> real)
        (f : complex # complex -> 'e) (x : complex # complex) <=>
        ?L : complex # complex -> 'e.
          q1050932_bounded_complex_linear_pair addE smulE normE L /\
          !epsilon : real.
            0 < epsilon ==>
            ?delta : real.
              0 < delta /\
              !h : complex # complex.
                0 < q1050932_pair_norm h /\
                q1050932_pair_norm h < delta
                ==>
                normE
                  (addE
                    (addE
                      (f (q1050932_pair_add x h))
                      (negE (f x)))
                    (negE (L h))) <
                epsilon * q1050932_pair_norm h``);

val q1050932_analytic_pair_at_def = new_definition (
  "q1050932_analytic_pair_at_def",
  ``q1050932_analytic_pair_at
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : complex -> 'e -> 'e) (normE : 'e -> real)
      (f : complex # complex -> 'e) (x : complex # complex) <=>
      ?radius : real.
        0 < radius /\
        !y : complex # complex.
          q1050932_pair_norm (q1050932_pair_sub y x) < radius ==>
          q1050932_complex_frechet_differentiable_pair_at
            addE negE smulE normE f y``);

val q1050932_analytic_on_nhd_pair_def = new_definition (
  "q1050932_analytic_on_nhd_pair_def",
  ``q1050932_analytic_on_nhd_pair
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : complex -> 'e -> 'e) (normE : 'e -> real)
      (f : complex # complex -> 'e)
      (s : (complex # complex) set) <=>
      !x : complex # complex.
        x IN s ==>
        q1050932_analytic_pair_at
          addE negE smulE normE f x``);

val Pair_hartogs =
  ``!(zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (smulE : complex -> 'e -> 'e)
      (normE : 'e -> real)
      (f : complex # complex -> 'e)
      (s : (complex # complex) set).
      q1050932_normed_complex_space zeroE addE negE smulE normE /\
      q1050932_complete addE negE normE /\
      q1050932_second_countable addE negE normE /\
      q1050932_open_in_pair s /\
      (!c0 c1.
        (c0,c1) IN s ==>
        q1050932_analytic_one_at
          addE negE smulE normE
          (\z0. f (z0,c1)) c0) /\
      (!c0 c1.
        (c0,c1) IN s ==>
        q1050932_analytic_one_at
          addE negE smulE normE
          (\z1. f (c0,z1)) c1)
      ==>
      q1050932_analytic_on_nhd_pair
        addE negE smulE normE f s``;

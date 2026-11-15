(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q967972 (thousand-theorems__hol4__Q967972), "Open mapping theorem (complex
  analysis)": a complex-analytic function from a complex normed space to the
  complex numbers is either constant on a preconnected set or maps every open
  subset of that set to an open subset of the complex plane. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory complexTheory;

val q967972_normed_complex_space_def = new_definition (
  "q967972_normed_complex_space_def",
  ``q967972_normed_complex_space
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
      (!x. normE (negE x) = normE x) /\
      (!x y. normE (addE x y) <= normE x + normE y) /\
      (!a x. normE (smulE a x) = modu a * normE x)``);

val q967972_bounded_complex_linear_def = new_definition (
  "q967972_bounded_complex_linear_def",
  ``q967972_bounded_complex_linear
      (addE : 'e -> 'e -> 'e) (smulE : complex -> 'e -> 'e)
      (normE : 'e -> real) (L : 'e -> complex) <=>
      (!x y. L (addE x y) = L x + L y) /\
      (!a x. L (smulE a x) = a * L x) /\
      ?C : real.
        0 <= C /\ !x. modu (L x) <= C * normE x``);

val q967972_complex_frechet_differentiable_at_def = new_definition (
  "q967972_complex_frechet_differentiable_at_def",
  ``q967972_complex_frechet_differentiable_at
      (addE : 'e -> 'e -> 'e) (smulE : complex -> 'e -> 'e)
      (normE : 'e -> real) (g : 'e -> complex) (x : 'e) <=>
      ?L : 'e -> complex.
        q967972_bounded_complex_linear addE smulE normE L /\
        !epsilon : real.
          0 < epsilon ==>
          ?delta : real.
            0 < delta /\
            !h : 'e.
              0 < normE h /\ normE h < delta
              ==>
              modu (g (addE x h) - g x - L h) <
                epsilon * normE h``);

val q967972_analytic_on_nhd_def = new_definition (
  "q967972_analytic_on_nhd_def",
  ``q967972_analytic_on_nhd
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : complex -> 'e -> 'e) (normE : 'e -> real)
      (g : 'e -> complex) (U : 'e -> bool) <=>
      !x : 'e.
        U x ==>
        ?radius : real.
          0 < radius /\
          !y : 'e.
            normE (addE y (negE x)) < radius
            ==>
            q967972_complex_frechet_differentiable_at
              addE smulE normE g y``);

val q967972_is_open_def = new_definition (
  "q967972_is_open_def",
  ``q967972_is_open
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) (s : 'a -> bool) <=>
      !x : 'a.
        s x ==>
        ?radius : real.
          0 < radius /\
          !y : 'a.
            norm (add y (neg x)) < radius ==> s y``);

val q967972_preconnected_def = new_definition (
  "q967972_preconnected_def",
  ``q967972_preconnected
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (normE : 'e -> real) (U : 'e -> bool) <=>
      !u v : 'e -> bool.
        q967972_is_open addE negE normE u /\
        q967972_is_open addE negE normE v /\
        (!x. U x ==> u x \/ v x) /\
        (?x. U x /\ u x) /\
        (?x. U x /\ v x)
        ==>
        ?x. U x /\ u x /\ v x``);

val AnalyticOnNhd_is_constant_or_isOpen =
  ``!(zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (smulE : complex -> 'e -> 'e)
      (normE : 'e -> real) (U : 'e -> bool)
      (g : 'e -> complex).
      q967972_normed_complex_space zeroE addE negE smulE normE /\
      q967972_analytic_on_nhd addE negE smulE normE g U /\
      q967972_preconnected addE negE normE U
      ==>
      (?w : complex. !z : 'e. U z ==> g z = w) \/
      !s : 'e -> bool.
        (!z. s z ==> U z) /\
        q967972_is_open addE negE normE s
        ==>
        q967972_is_open
          (\z w. z + w) (\z. -z) modu
          (\w : complex. ?z : 'e. s z /\ g z = w)``;

(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q834025, "Cauchy integral theorem": the Cauchy integral formula on a
  complex circle for a function continuous on the closed disc and complex
  differentiable in its interior outside a countable set. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory transcTheory complexTheory;
open integralTheory;

val q834025_countable_def = new_definition (
  "q834025_countable_def",
  ``q834025_countable (s : complex set) <=>
      ?encode : complex -> num.
        INJ encode s (UNIV : num set)``);

val q834025_open_ball_def = new_definition (
  "q834025_open_ball_def",
  ``q834025_open_ball (c : complex) (R : real) (z : complex) <=>
      modu (z - c) < R``);

val q834025_closed_ball_def = new_definition (
  "q834025_closed_ball_def",
  ``q834025_closed_ball (c : complex) (R : real) (z : complex) <=>
      modu (z - c) <= R``);

val q834025_continuous_on_closed_ball_def = new_definition (
  "q834025_continuous_on_closed_ball_def",
  ``q834025_continuous_on_closed_ball
      (f : complex -> complex) (c : complex) (R : real) <=>
      !x : complex.
        q834025_closed_ball c R x ==>
        !epsilon : real.
          0 < epsilon ==>
          ?delta : real.
            0 < delta /\
            !y : complex.
              q834025_closed_ball c R y /\
              modu (y - x) < delta
              ==>
              modu (f y - f x) < epsilon``);

val q834025_complex_differentiable_at_def = new_definition (
  "q834025_complex_differentiable_at_def",
  ``q834025_complex_differentiable_at
      (f : complex -> complex) (x : complex) <=>
      ?derivative : complex.
        !epsilon : real.
          0 < epsilon ==>
          ?delta : real.
            0 < delta /\
            !h : complex.
              0 < modu h /\ modu h < delta
              ==>
              modu
                (f (x + h) - f x - derivative * h) <
              epsilon * modu h``);

val q834025_circle_map_def = new_definition (
  "q834025_circle_map_def",
  ``q834025_circle_map
      (c : complex) (R : real) (theta : real) =
      c +
      complex_of_real R *
        complex_exp (complex_of_real theta * i)``);

val q834025_circle_velocity_def = new_definition (
  "q834025_circle_velocity_def",
  ``q834025_circle_velocity (R : real) (theta : real) =
      complex_of_real R * i *
        complex_exp (complex_of_real theta * i)``);

val q834025_circle_integrand_def = new_definition (
  "q834025_circle_integrand_def",
  ``q834025_circle_integrand
      (g : complex -> complex) (c : complex) (R : real) (theta : real) =
      g (q834025_circle_map c R theta) *
        q834025_circle_velocity R theta``);

val q834025_circle_integral_def = new_definition (
  "q834025_circle_integral_def",
  ``q834025_circle_integral
      (g : complex -> complex) (c : complex) (R : real) =
      ((integral (0,2 * pi)
          (\theta. RE (q834025_circle_integrand g c R theta)),
        integral (0,2 * pi)
          (\theta. IM (q834025_circle_integrand g c R theta))) :
        complex)``);

val circleIntegral_div_sub_of_differentiable_on_off_countable =
  ``!(R : real) (c : complex) (w : complex) (s : complex set)
      (f : complex -> complex).
      q834025_countable s /\
      q834025_open_ball c R w /\
      q834025_continuous_on_closed_ball f c R /\
      (!z : complex.
        q834025_open_ball c R z /\ ~(z IN s)
        ==>
        q834025_complex_differentiable_at f z)
      ==>
      q834025_circle_integral (\z. f z / (z - w)) c R =
        complex_of_real (2 * pi) * i * f w``;

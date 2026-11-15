(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q4378868 (thousand-theorems__hol4__Q4378868), "Phragmén–Lindelöf theorem":
  an E-valued function differentiable on an open horizontal strip and
  continuous on its closure, with sufficiently slow double-exponential growth
  and boundary norm bounded by C, has norm at most C throughout the closed
  strip. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory transcTheory complexTheory;

val q4378868_normed_complex_space_def = new_definition (
  "q4378868_normed_complex_space_def",
  ``q4378868_normed_complex_space
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : complex -> 'e -> 'e) (norm : 'e -> real) <=>
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x. smul 1 x = x) /\
      (!a b x. smul (a * b) x = smul a (smul b x)) /\
      (!a b x. smul (a + b) x = add (smul a x) (smul b x)) /\
      (!a x y. smul a (add x y) = add (smul a x) (smul a y)) /\
      (!x. smul 0 x = zero) /\
      (!a. smul a zero = zero) /\
      (!x. neg x = smul (-1) x) /\
      (!x. 0 <= norm x) /\
      (!x. (norm x = 0) <=> (x = zero)) /\
      (!x. norm (neg x) = norm x) /\
      (!x y. norm (add x y) <= norm x + norm y) /\
      (!a x. norm (smul a x) = modu a * norm x)``);

val q4378868_in_horizontal_strip_def = new_definition (
  "q4378868_in_horizontal_strip_def",
  ``q4378868_in_horizontal_strip
      (a : real) (b : real) (z : complex) <=>
      a < IM z /\ IM z < b``);

val q4378868_in_horizontal_strip_closure_def = new_definition (
  "q4378868_in_horizontal_strip_closure_def",
  ``q4378868_in_horizontal_strip_closure
      (a : real) (b : real) (z : complex) <=>
      a < b /\ a <= IM z /\ IM z <= b``);

val q4378868_continuous_on_strip_closure_def = new_definition (
  "q4378868_continuous_on_strip_closure_def",
  ``q4378868_continuous_on_strip_closure
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (f : complex -> 'e)
      (a : real) (b : real) <=>
      !x.
        q4378868_in_horizontal_strip_closure a b x ==>
        !epsilon : real.
          0 < epsilon ==>
          ?delta : real.
            0 < delta /\
            !y.
              q4378868_in_horizontal_strip_closure a b y /\
              modu (y - x) < delta
              ==>
              norm (add (f y) (neg (f x))) < epsilon``);

val q4378868_complex_differentiable_on_strip_def = new_definition (
  "q4378868_complex_differentiable_on_strip_def",
  ``q4378868_complex_differentiable_on_strip
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : complex -> 'e -> 'e) (norm : 'e -> real)
      (f : complex -> 'e) (a : real) (b : real) <=>
      !x.
        q4378868_in_horizontal_strip a b x ==>
        ?deriv : 'e.
          !epsilon : real.
            0 < epsilon ==>
            ?delta : real.
              0 < delta /\
              !h : complex.
                0 < modu h /\ modu h < delta
                ==>
                norm
                  (add
                    (add (f (x + h)) (neg (f x)))
                    (neg (smul h deriv))) <
                epsilon * modu h``);

val q4378868_diff_cont_on_cl_def = new_definition (
  "q4378868_diff_cont_on_cl_def",
  ``q4378868_diff_cont_on_cl
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : complex -> 'e -> 'e) (norm : 'e -> real)
      (f : complex -> 'e) (a : real) (b : real) <=>
      q4378868_complex_differentiable_on_strip
        add neg smul norm f a b /\
      q4378868_continuous_on_strip_closure
        add neg norm f a b``);

val q4378868_double_exp_big_o_on_strip_def = new_definition (
  "q4378868_double_exp_big_o_on_strip_def",
  ``q4378868_double_exp_big_o_on_strip
      (norm : 'e -> real) (f : complex -> 'e)
      (a : real) (b : real) (c : real) (B : real) <=>
      ?A R : real.
        0 < A /\
        !w.
          R <= abs (RE w) /\
          q4378868_in_horizontal_strip a b w
          ==>
          norm (f w) <=
            A * exp (B * exp (c * abs (RE w)))``);

val PhragmenLindelof_horizontal_strip =
  ``!(zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : complex -> 'e -> 'e) (norm : 'e -> real)
      (a : real) (b : real) (C : real)
      (f : complex -> 'e) (z : complex).
      q4378868_normed_complex_space zero add neg smul norm /\
      q4378868_diff_cont_on_cl add neg smul norm f a b /\
      (?c : real.
        c < pi / (b - a) /\
        ?B : real.
          q4378868_double_exp_big_o_on_strip norm f a b c B) /\
      (!w : complex. IM w = a ==> norm (f w) <= C) /\
      (!w : complex. IM w = b ==> norm (f w) <= C) /\
      a <= IM z /\
      IM z <= b
      ==>
      norm (f z) <= C``;

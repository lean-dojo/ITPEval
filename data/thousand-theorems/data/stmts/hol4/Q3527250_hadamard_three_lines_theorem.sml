(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q3527250, "Hadamard three-lines theorem": a bounded complex-differentiable
  function on a vertical strip is bounded by the complex interpolation of
  the suprema of its boundary norms. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory transcTheory complexTheory;

val q3527250_normed_complex_space_def = new_definition (
  "q3527250_normed_complex_space_def",
  ``q3527250_normed_complex_space
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

val q3527250_in_vertical_strip_def = new_definition (
  "q3527250_in_vertical_strip_def",
  ``q3527250_in_vertical_strip (l : real) (u : real) (z : complex) <=>
      l < RE z /\ RE z < u``);

val q3527250_in_vertical_closed_strip_def = new_definition (
  "q3527250_in_vertical_closed_strip_def",
  ``q3527250_in_vertical_closed_strip
      (l : real) (u : real) (z : complex) <=>
      l <= RE z /\ RE z <= u``);

val q3527250_continuous_on_closed_strip_def = new_definition (
  "q3527250_continuous_on_closed_strip_def",
  ``q3527250_continuous_on_closed_strip
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (f : complex -> 'e)
      (l : real) (u : real) <=>
      !x.
        q3527250_in_vertical_closed_strip l u x ==>
        !epsilon : real.
          0 < epsilon ==>
          ?delta : real.
            0 < delta /\
            !y.
              q3527250_in_vertical_closed_strip l u y /\
              modu (y - x) < delta
              ==>
              norm (add (f y) (neg (f x))) < epsilon``);

val q3527250_complex_differentiable_on_strip_def = new_definition (
  "q3527250_complex_differentiable_on_strip_def",
  ``q3527250_complex_differentiable_on_strip
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : complex -> 'e -> 'e) (norm : 'e -> real)
      (f : complex -> 'e) (l : real) (u : real) <=>
      !x.
        q3527250_in_vertical_strip l u x ==>
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

val q3527250_diff_cont_on_cl_def = new_definition (
  "q3527250_diff_cont_on_cl_def",
  ``q3527250_diff_cont_on_cl
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : complex -> 'e -> 'e) (norm : 'e -> real)
      (f : complex -> 'e) (l : real) (u : real) <=>
      q3527250_complex_differentiable_on_strip
        add neg smul norm f l u /\
      q3527250_continuous_on_closed_strip
        add neg norm f l u``);

val q3527250_bounded_on_closed_strip_def = new_definition (
  "q3527250_bounded_on_closed_strip_def",
  ``q3527250_bounded_on_closed_strip
      (norm : 'e -> real) (f : complex -> 'e)
      (l : real) (u : real) <=>
      ?B : real.
        !w.
          q3527250_in_vertical_closed_strip l u w ==>
          norm (f w) <= B``);

val q3527250_sSupNormIm_def = new_definition (
  "q3527250_sSupNormIm_def",
  ``q3527250_sSupNormIm
      (norm : 'e -> real) (f : complex -> 'e) (x : real) =
      sup
        (\r : real.
          ?w : complex.
            RE w = x /\ r = norm (f w))``);

val q3527250_positive_real_cpow_def = new_definition (
  "q3527250_positive_real_cpow_def",
  ``q3527250_positive_real_cpow (r : real) (z : complex) =
      complex_exp (complex_of_real (ln r) * z)``);

val q3527250_interpStrip_def = new_definition (
  "q3527250_interpStrip_def",
  ``q3527250_interpStrip
      (norm : 'e -> real) (f : complex -> 'e)
      (l : real) (u : real) (z : complex) =
      let ml = q3527250_sSupNormIm norm f l in
      let mu = q3527250_sSupNormIm norm f u in
        if ml = 0 \/ mu = 0 then
          0
        else
          q3527250_positive_real_cpow ml
            (1 -
              (z - complex_of_real l) /
                (complex_of_real u - complex_of_real l)) *
          q3527250_positive_real_cpow mu
            ((z - complex_of_real l) /
              (complex_of_real u - complex_of_real l))``);

val norm_le_interpStrip_of_mem_verticalClosedStrip =
  ``!(zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : complex -> 'e -> 'e) (norm : 'e -> real)
      (l : real) (u : real) (f : complex -> 'e) (z : complex).
      q3527250_normed_complex_space zero add neg smul norm /\
      l < u /\
      q3527250_in_vertical_closed_strip l u z /\
      q3527250_diff_cont_on_cl add neg smul norm f l u /\
      q3527250_bounded_on_closed_strip norm f l u
      ==>
      norm (f z) <=
        modu (q3527250_interpStrip norm f l u z)``;

(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q576478 (thousand-theorems__hol4__Q576478), "Liouville's theorem (complex
  analysis)": an everywhere complex Fréchet-differentiable function between
  complex normed spaces with bounded range takes the same value at every two
  points. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory complexTheory;

val q576478_normed_complex_space_def = new_definition (
  "q576478_normed_complex_space_def",
  ``q576478_normed_complex_space
      (zero : 'a) (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (smul : complex -> 'a -> 'a) (norm : 'a -> real) <=>
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

val q576478_bounded_complex_linear_def = new_definition (
  "q576478_bounded_complex_linear_def",
  ``q576478_bounded_complex_linear
      (addE : 'e -> 'e -> 'e) (smulE : complex -> 'e -> 'e)
      (normE : 'e -> real)
      (addF : 'f -> 'f -> 'f) (smulF : complex -> 'f -> 'f)
      (normF : 'f -> real) (L : 'e -> 'f) <=>
      (!x y. L (addE x y) = addF (L x) (L y)) /\
      (!a x. L (smulE a x) = smulF a (L x)) /\
      ?C : real.
        0 <= C /\ !x. normF (L x) <= C * normE x``);

val q576478_complex_differentiable_def = new_definition (
  "q576478_complex_differentiable_def",
  ``q576478_complex_differentiable
      (addE : 'e -> 'e -> 'e) (normE : 'e -> real)
      (addF : 'f -> 'f -> 'f) (negF : 'f -> 'f)
      (smulE : complex -> 'e -> 'e)
      (smulF : complex -> 'f -> 'f) (normF : 'f -> real)
      (f : 'e -> 'f) <=>
      !x : 'e.
        ?L : 'e -> 'f.
          q576478_bounded_complex_linear
            addE smulE normE addF smulF normF L /\
          !epsilon : real.
            0 < epsilon ==>
            ?delta : real.
              0 < delta /\
              !h : 'e.
                0 < normE h /\ normE h < delta
                ==>
                normF
                  (addF
                    (addF (f (addE x h)) (negF (f x)))
                    (negF (L h))) <
                epsilon * normE h``);

val q576478_bounded_range_def = new_definition (
  "q576478_bounded_range_def",
  ``q576478_bounded_range (normF : 'f -> real) (f : 'e -> 'f) <=>
      ?C : real. 0 <= C /\ !x : 'e. normF (f x) <= C``);

val Differentiable_apply_eq_apply_of_bounded =
  ``!(zeroE : 'e) (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : complex -> 'e -> 'e) (normE : 'e -> real)
      (zeroF : 'f) (addF : 'f -> 'f -> 'f) (negF : 'f -> 'f)
      (smulF : complex -> 'f -> 'f) (normF : 'f -> real)
      (f : 'e -> 'f) (z : 'e) (w : 'e).
      q576478_normed_complex_space zeroE addE negE smulE normE /\
      q576478_normed_complex_space zeroF addF negF smulF normF /\
      q576478_complex_differentiable
        addE normE addF negF smulE smulF normF f /\
      q576478_bounded_range normF f
      ==>
      f z = f w``;

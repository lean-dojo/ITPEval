(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1660147 (thousand-theorems__hol4__Q1660147), "Mazur–Ulam theorem":
  every bijective isometry between real normed affine spaces is an affine
  isometry equivalence with the same underlying map. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val q1660147_normed_real_vector_space_def = new_definition (
  "q1660147_normed_real_vector_space_def",
  ``q1660147_normed_real_vector_space
      (zero : 'v) (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v) (norm : 'v -> real) <=>
      (!x y. add x y = add y x) /\
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x. add x zero = x) /\
      (!x. add x (neg x) = zero) /\
      (!x. 0 <= norm x) /\
      (!x. (norm x = 0) <=> (x = zero)) /\
      (!x. norm (neg x) = norm x) /\
      (!x y. norm (add x y) <= norm x + norm y) /\
      (!x. smul 1 x = x) /\
      (!a b x. smul (a * b) x = smul a (smul b x)) /\
      (!a b x. smul (a + b) x = add (smul a x) (smul b x)) /\
      (!a x y. smul a (add x y) = add (smul a x) (smul a y)) /\
      (!x. smul 0 x = zero) /\
      (!a. smul a zero = zero) /\
      (!a x. norm (smul a x) = abs a * norm x)``);

val q1660147_normed_add_torsor_def = new_definition (
  "q1660147_normed_add_torsor_def",
  ``q1660147_normed_add_torsor
      (zero : 'v) (add : 'v -> 'v -> 'v)
      (vadd : 'v -> 'p -> 'p) (vsub : 'p -> 'p -> 'v) <=>
      (!p. vadd zero p = p) /\
      (!u v p. vadd (add u v) p = vadd u (vadd v p)) /\
      (!p q. vadd (vsub p q) q = p) /\
      (!v p. vsub (vadd v p) p = v)``);

val q1660147_isometry_equiv_def = new_definition (
  "q1660147_isometry_equiv_def",
  ``q1660147_isometry_equiv
      (normE : 'e -> real) (vsubE : 'pe -> 'pe -> 'e)
      (normF : 'f -> real) (vsubF : 'pf -> 'pf -> 'f)
      (forward : 'pe -> 'pf) (inverse : 'pf -> 'pe) <=>
      (!p q.
        normF (vsubF (forward p) (forward q)) =
        normE (vsubE p q)) /\
      (!p. inverse (forward p) = p) /\
      (!q. forward (inverse q) = q)``);

val q1660147_linear_isometry_equiv_def = new_definition (
  "q1660147_linear_isometry_equiv_def",
  ``q1660147_linear_isometry_equiv
      (addE : 'e -> 'e -> 'e) (smulE : real -> 'e -> 'e)
      (normE : 'e -> real)
      (addF : 'f -> 'f -> 'f) (smulF : real -> 'f -> 'f)
      (normF : 'f -> real)
      (forward : 'e -> 'f) (inverse : 'f -> 'e) <=>
      (!x y. forward (addE x y) = addF (forward x) (forward y)) /\
      (!a x. forward (smulE a x) = smulF a (forward x)) /\
      (!x. normF (forward x) = normE x) /\
      (!x. inverse (forward x) = x) /\
      (!y. forward (inverse y) = y)``);

val coe_toRealAffineIsometryEquiv =
  ``!(zeroE : 'e) (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : real -> 'e -> 'e) (normE : 'e -> real)
      (zeroF : 'f) (addF : 'f -> 'f -> 'f) (negF : 'f -> 'f)
      (smulF : real -> 'f -> 'f) (normF : 'f -> real)
      (vaddE : 'e -> 'pe -> 'pe) (vsubE : 'pe -> 'pe -> 'e)
      (vaddF : 'f -> 'pf -> 'pf) (vsubF : 'pf -> 'pf -> 'f)
      (forward : 'pe -> 'pf) (inverse : 'pf -> 'pe).
      q1660147_normed_real_vector_space
        zeroE addE negE smulE normE /\
      q1660147_normed_real_vector_space
        zeroF addF negF smulF normF /\
      q1660147_normed_add_torsor zeroE addE vaddE vsubE /\
      q1660147_normed_add_torsor zeroF addF vaddF vsubF /\
      q1660147_isometry_equiv
        normE vsubE normF vsubF forward inverse
      ==>
      ?linear inverseLinear.
        q1660147_linear_isometry_equiv
          addE smulE normE addF smulF normF
          linear inverseLinear /\
        !p v.
          forward (vaddE v p) =
          vaddF (linear v) (forward p)``;

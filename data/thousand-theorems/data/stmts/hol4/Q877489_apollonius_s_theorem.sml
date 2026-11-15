(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q877489 (thousand-theorems__hol4__Q877489), "Apollonius's theorem":
  in an arbitrary real inner-product affine space, the sum of the squared
  distances from a point to two endpoints equals twice the sum of its squared
  distance to their midpoint and the squared half-distance between them.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val q877489_real_inner_affine_space_def = new_definition (
  "q877489_real_inner_affine_space_def",
  ``q877489_real_inner_affine_space
      (zero : 'v)
      (add : 'v -> 'v -> 'v)
      (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v)
      (inner : 'v -> 'v -> real)
      (vadd : 'v -> 'p -> 'p)
      (vsub : 'p -> 'p -> 'v) <=>
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x. smul 1 x = x) /\
      (!r s x. smul (r * s) x = smul r (smul s x)) /\
      (!r s x. smul (r + s) x = add (smul r x) (smul s x)) /\
      (!r x y. smul r (add x y) = add (smul r x) (smul r y)) /\
      (!x. smul 0 x = zero) /\
      (!r. smul r zero = zero) /\
      (!x y. inner x y = inner y x) /\
      (!x y z. inner (add x y) z = inner x z + inner y z) /\
      (!r x y. inner (smul r x) y = r * inner x y) /\
      (!x. 0 <= inner x x) /\
      (!x. (inner x x = 0 <=> x = zero)) /\
      (!p. vadd zero p = p) /\
      (!u v p. vadd (add u v) p = vadd u (vadd v p)) /\
      (!p q. vadd (vsub p q) q = p) /\
      (!v p. vsub (vadd v p) p = v)``);

val q877489_norm_def = new_definition (
  "q877489_norm_def",
  ``q877489_norm (inner : 'v -> 'v -> real) (x : 'v) =
      sqrt (inner x x)``);

val q877489_dist_def = new_definition (
  "q877489_dist_def",
  ``q877489_dist
      (inner : 'v -> 'v -> real)
      (vsub : 'p -> 'p -> 'v)
      (x : 'p)
      (y : 'p) =
      q877489_norm inner (vsub x y)``);

val q877489_midpoint_def = new_definition (
  "q877489_midpoint_def",
  ``q877489_midpoint
      (smul : real -> 'v -> 'v)
      (vadd : 'v -> 'p -> 'p)
      (vsub : 'p -> 'p -> 'v)
      (x : 'p)
      (y : 'p) =
      vadd (smul (1 / 2) (vsub x y)) y``);

val dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq =
  ``!(zero : 'v)
      (add : 'v -> 'v -> 'v)
      (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v)
      (inner : 'v -> 'v -> real)
      (vadd : 'v -> 'p -> 'p)
      (vsub : 'p -> 'p -> 'v)
      (a b c : 'p).
      q877489_real_inner_affine_space
        zero add neg smul inner vadd vsub
      ==>
      q877489_dist inner vsub a b pow 2 +
          q877489_dist inner vsub a c pow 2 =
        2 *
          (q877489_dist inner vsub a
              (q877489_midpoint smul vadd vsub b c) pow 2 +
           (q877489_dist inner vsub b c / 2) pow 2)``;

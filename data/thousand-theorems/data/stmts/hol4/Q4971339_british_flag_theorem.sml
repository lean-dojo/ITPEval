(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q4971339 (thousand-theorems__hol4__Q4971339), "British flag theorem":
  in an arbitrary real inner-product affine space, a parallelogram with a
  right angle satisfies the opposite-corner squared-distance identity for
  every point. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val q4971339_real_inner_affine_space_def = new_definition (
  "q4971339_real_inner_affine_space_def",
  ``q4971339_real_inner_affine_space
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

val q4971339_norm_def = new_definition (
  "q4971339_norm_def",
  ``q4971339_norm (inner : 'v -> 'v -> real) (x : 'v) =
      sqrt (inner x x)``);

val q4971339_dist_def = new_definition (
  "q4971339_dist_def",
  ``q4971339_dist
      (inner : 'v -> 'v -> real)
      (vsub : 'p -> 'p -> 'v)
      (x : 'p)
      (y : 'p) =
      q4971339_norm inner (vsub x y)``);

val q4971339_midpoint_def = new_definition (
  "q4971339_midpoint_def",
  ``q4971339_midpoint
      (smul : real -> 'v -> 'v)
      (vadd : 'v -> 'p -> 'p)
      (vsub : 'p -> 'p -> 'v)
      (x : 'p)
      (y : 'p) =
      vadd (smul (1 / 2) (vsub x y)) y``);

val q4971339_angle_def = new_definition (
  "q4971339_angle_def",
  ``q4971339_angle
      (inner : 'v -> 'v -> real)
      (vsub : 'p -> 'p -> 'v)
      (x : 'p)
      (y : 'p)
      (z : 'p) =
      acs
        (inner (vsub x y) (vsub z y) /
          (q4971339_norm inner (vsub x y) *
           q4971339_norm inner (vsub z y)))``);

val dist_sq_add_dist_sq_eq_dist_sq_add_dist_sq_of_angle_eq_pi_div_two =
  ``!(zero : 'v)
      (add : 'v -> 'v -> 'v)
      (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v)
      (inner : 'v -> 'v -> real)
      (vadd : 'v -> 'p -> 'p)
      (vsub : 'p -> 'p -> 'v)
      (a b c d p : 'p).
      q4971339_real_inner_affine_space
        zero add neg smul inner vadd vsub /\
      q4971339_midpoint smul vadd vsub a c =
        q4971339_midpoint smul vadd vsub b d /\
      q4971339_angle inner vsub b a d = pi / 2
      ==>
      q4971339_dist inner vsub p a pow 2 +
          q4971339_dist inner vsub p c pow 2 =
        q4971339_dist inner vsub p b pow 2 +
          q4971339_dist inner vsub p d pow 2``;

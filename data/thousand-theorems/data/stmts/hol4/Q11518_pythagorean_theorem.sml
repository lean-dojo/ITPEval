(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q11518, "Pythagorean theorem": in an arbitrary real inner-product affine
  space, the squared-distance identity for three points holds if and only if
  their angle at the middle point is pi / 2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val q11518_real_inner_affine_space_def = new_definition (
  "q11518_real_inner_affine_space_def",
  ``q11518_real_inner_affine_space
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

val q11518_norm_def = new_definition (
  "q11518_norm_def",
  ``q11518_norm (inner : 'v -> 'v -> real) (x : 'v) =
      sqrt (inner x x)``);

val q11518_dist_def = new_definition (
  "q11518_dist_def",
  ``q11518_dist
      (inner : 'v -> 'v -> real)
      (vsub : 'p -> 'p -> 'v)
      (p : 'p)
      (q : 'p) =
      q11518_norm inner (vsub p q)``);

val q11518_angle_def = new_definition (
  "q11518_angle_def",
  ``q11518_angle
      (inner : 'v -> 'v -> real)
      (vsub : 'p -> 'p -> 'v)
      (p : 'p)
      (q : 'p)
      (r : 'p) =
      acs
        (inner (vsub p q) (vsub r q) /
          (q11518_norm inner (vsub p q) *
           q11518_norm inner (vsub r q)))``);

val dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two =
  ``!(zero : 'v)
      (add : 'v -> 'v -> 'v)
      (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v)
      (inner : 'v -> 'v -> real)
      (vadd : 'v -> 'p -> 'p)
      (vsub : 'p -> 'p -> 'v)
      (p1 p2 p3 : 'p).
      q11518_real_inner_affine_space
        zero add neg smul inner vadd vsub
      ==>
      (q11518_dist inner vsub p1 p3 *
         q11518_dist inner vsub p1 p3 =
       q11518_dist inner vsub p1 p2 *
         q11518_dist inner vsub p1 p2 +
       q11518_dist inner vsub p3 p2 *
         q11518_dist inner vsub p3 p2
       <=>
       q11518_angle inner vsub p1 p2 p3 = pi / 2)``;

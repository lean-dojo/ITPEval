(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q2267175 (thousand-theorems__hol4__Q2267175), "Tangent-secant theorem":
  in an arbitrary real inner-product affine space, the squared distance from
  a point to a tangent point of a sphere equals the product of its distances
  to two sphere points on a secant line. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val q2267175_real_inner_affine_space_def = new_definition (
  "q2267175_real_inner_affine_space_def",
  ``q2267175_real_inner_affine_space
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
      (!r x y. smul r (add x y) = add (smul r x) (smul r y)) /\
      (!r s x. smul (r + s) x = add (smul r x) (smul s x)) /\
      (!x. smul 0 x = zero) /\
      (!r. smul r zero = zero) /\
      (!x y z. inner (add x y) z = inner x z + inner y z) /\
      (!r x y. inner (smul r x) y = r * inner x y) /\
      (!x y. inner x y = inner y x) /\
      (!x. 0 <= inner x x) /\
      (!x. (inner x x = 0 <=> x = zero)) /\
      (!p. vadd zero p = p) /\
      (!u v p. vadd (add u v) p = vadd u (vadd v p)) /\
      (!p q. vadd (vsub p q) q = p) /\
      (!v p. vsub (vadd v p) p = v)``);

val q2267175_norm_def = new_definition (
  "q2267175_norm_def",
  ``q2267175_norm (inner : 'v -> 'v -> real) (x : 'v) =
      sqrt (inner x x)``);

val q2267175_dist_def = new_definition (
  "q2267175_dist_def",
  ``q2267175_dist
      (inner : 'v -> 'v -> real)
      (vsub : 'p -> 'p -> 'v)
      (x : 'p)
      (y : 'p) =
      q2267175_norm inner (vsub x y)``);

val q2267175_on_sphere_def = new_definition (
  "q2267175_on_sphere_def",
  ``q2267175_on_sphere
      (inner : 'v -> 'v -> real)
      (vsub : 'p -> 'p -> 'v)
      (centre : 'p)
      (radius : real)
      (x : 'p) <=>
      q2267175_dist inner vsub x centre = radius``);

val q2267175_on_line_def = new_definition (
  "q2267175_on_line_def",
  ``q2267175_on_line
      (smul : real -> 'v -> 'v)
      (vadd : 'v -> 'p -> 'p)
      (vsub : 'p -> 'p -> 'v)
      (a : 'p)
      (b : 'p)
      (x : 'p) <=>
      ?r : real. x = vadd (smul r (vsub b a)) a``);

val q2267175_is_tangent_at_def = new_definition (
  "q2267175_is_tangent_at_def",
  ``q2267175_is_tangent_at
      (smul : real -> 'v -> 'v)
      (inner : 'v -> 'v -> real)
      (vadd : 'v -> 'p -> 'p)
      (vsub : 'p -> 'p -> 'v)
      (centre : 'p)
      (radius : real)
      (t : 'p)
      (p : 'p) <=>
      q2267175_on_sphere inner vsub centre radius t /\
      q2267175_on_line smul vadd vsub p t t /\
      (!x.
         q2267175_on_line smul vadd vsub p t x
         ==>
         inner (vsub x t) (vsub t centre) = 0)``);

val q2267175_tangent_secant_theorem =
  ``!(zero : 'v)
      (add : 'v -> 'v -> 'v)
      (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v)
      (inner : 'v -> 'v -> real)
      (vadd : 'v -> 'p -> 'p)
      (vsub : 'p -> 'p -> 'v)
      (centre : 'p)
      (radius : real)
      (a b t p : 'p).
      q2267175_real_inner_affine_space
        zero add neg smul inner vadd vsub /\
      q2267175_on_sphere inner vsub centre radius a /\
      q2267175_on_sphere inner vsub centre radius b /\
      q2267175_on_line smul vadd vsub a b p /\
      q2267175_is_tangent_at
        smul inner vadd vsub centre radius t p
      ==>
      q2267175_dist inner vsub p t pow 2 =
        q2267175_dist inner vsub p a *
        q2267175_dist inner vsub p b``;

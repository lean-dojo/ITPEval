(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q739403 (thousand-theorems__hol4__Q739403), "Stewart's theorem": in an
  arbitrary real inner-product affine space, a cevian whose endpoint forms a
  straight angle on the opposite side satisfies Stewart's distance identity.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val q739403_real_inner_affine_space_def = new_definition (
  "q739403_real_inner_affine_space_def",
  ``q739403_real_inner_affine_space
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

val q739403_norm_def = new_definition (
  "q739403_norm_def",
  ``q739403_norm (inner : 'v -> 'v -> real) (x : 'v) =
      sqrt (inner x x)``);

val q739403_dist_def = new_definition (
  "q739403_dist_def",
  ``q739403_dist
      (inner : 'v -> 'v -> real)
      (vsub : 'p -> 'p -> 'v)
      (x : 'p)
      (y : 'p) =
      q739403_norm inner (vsub x y)``);

val q739403_angle_def = new_definition (
  "q739403_angle_def",
  ``q739403_angle
      (inner : 'v -> 'v -> real)
      (vsub : 'p -> 'p -> 'v)
      (x : 'p)
      (y : 'p)
      (z : 'p) =
      acs
        (inner (vsub x y) (vsub z y) /
          (q739403_norm inner (vsub x y) *
           q739403_norm inner (vsub z y)))``);

val dist_sq_mul_dist_add_dist_sq_mul_dist =
  ``!(zero : 'v)
      (add : 'v -> 'v -> 'v)
      (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v)
      (inner : 'v -> 'v -> real)
      (vadd : 'v -> 'p -> 'p)
      (vsub : 'p -> 'p -> 'v)
      (a b c p : 'p).
      q739403_real_inner_affine_space
        zero add neg smul inner vadd vsub /\
      q739403_angle inner vsub b p c = pi
      ==>
      q739403_dist inner vsub a b pow 2 *
          q739403_dist inner vsub c p +
        q739403_dist inner vsub a c pow 2 *
          q739403_dist inner vsub b p =
        q739403_dist inner vsub b c *
          (q739403_dist inner vsub a p pow 2 +
           q739403_dist inner vsub b p *
             q739403_dist inner vsub c p)``;

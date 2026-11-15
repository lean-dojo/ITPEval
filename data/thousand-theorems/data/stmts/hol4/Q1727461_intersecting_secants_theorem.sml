(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1727461 (thousand-theorems__hol4__Q1727461), "Intersecting secants
  theorem": in an arbitrary real inner-product affine space, two pairs of
  distinct cospherical points lying on same-direction rays from a point have
  equal products of their distances from that point. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val q1727461_real_inner_affine_space_def = new_definition (
  "q1727461_real_inner_affine_space_def",
  ``q1727461_real_inner_affine_space
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

val q1727461_norm_def = new_definition (
  "q1727461_norm_def",
  ``q1727461_norm (inner : 'v -> 'v -> real) (x : 'v) =
      sqrt (inner x x)``);

val q1727461_dist_def = new_definition (
  "q1727461_dist_def",
  ``q1727461_dist
      (inner : 'v -> 'v -> real)
      (vsub : 'p -> 'p -> 'v)
      (x : 'p)
      (y : 'p) =
      q1727461_norm inner (vsub x y)``);

val q1727461_angle_def = new_definition (
  "q1727461_angle_def",
  ``q1727461_angle
      (inner : 'v -> 'v -> real)
      (vsub : 'p -> 'p -> 'v)
      (x : 'p)
      (y : 'p)
      (z : 'p) =
      acs
        (inner (vsub x y) (vsub z y) /
          (q1727461_norm inner (vsub x y) *
           q1727461_norm inner (vsub z y)))``);

val q1727461_cospherical_four_def = new_definition (
  "q1727461_cospherical_four_def",
  ``q1727461_cospherical_four
      (inner : 'v -> 'v -> real)
      (vsub : 'p -> 'p -> 'v)
      (a : 'p)
      (b : 'p)
      (c : 'p)
      (d : 'p) <=>
      ?centre : 'p. ?radius : real.
        q1727461_dist inner vsub a centre = radius /\
        q1727461_dist inner vsub b centre = radius /\
        q1727461_dist inner vsub c centre = radius /\
        q1727461_dist inner vsub d centre = radius``);

val mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero =
  ``!(zero : 'v)
      (add : 'v -> 'v -> 'v)
      (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v)
      (inner : 'v -> 'v -> real)
      (vadd : 'v -> 'p -> 'p)
      (vsub : 'p -> 'p -> 'v)
      (a b c d p : 'p).
      q1727461_real_inner_affine_space
        zero add neg smul inner vadd vsub /\
      q1727461_cospherical_four inner vsub a b c d /\
      a <> b /\
      c <> d /\
      q1727461_angle inner vsub a p b = 0 /\
      q1727461_angle inner vsub c p d = 0
      ==>
      q1727461_dist inner vsub a p *
          q1727461_dist inner vsub b p =
        q1727461_dist inner vsub c p *
          q1727461_dist inner vsub d p``;

(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q459547, "Ptolemy's theorem": in an arbitrary real inner-product affine
  space, four cospherical points whose diagonals form straight angles at a
  common point satisfy Ptolemy's distance identity. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val q459547_real_inner_affine_space_def = new_definition (
  "q459547_real_inner_affine_space_def",
  ``q459547_real_inner_affine_space
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

val q459547_norm_def = new_definition (
  "q459547_norm_def",
  ``q459547_norm (inner : 'v -> 'v -> real) (x : 'v) =
      sqrt (inner x x)``);

val q459547_dist_def = new_definition (
  "q459547_dist_def",
  ``q459547_dist
      (inner : 'v -> 'v -> real)
      (vsub : 'p -> 'p -> 'v)
      (x : 'p)
      (y : 'p) =
      q459547_norm inner (vsub x y)``);

val q459547_angle_def = new_definition (
  "q459547_angle_def",
  ``q459547_angle
      (inner : 'v -> 'v -> real)
      (vsub : 'p -> 'p -> 'v)
      (x : 'p)
      (y : 'p)
      (z : 'p) =
      acs
        (inner (vsub x y) (vsub z y) /
          (q459547_norm inner (vsub x y) *
           q459547_norm inner (vsub z y)))``);

val q459547_cospherical_four_def = new_definition (
  "q459547_cospherical_four_def",
  ``q459547_cospherical_four
      (inner : 'v -> 'v -> real)
      (vsub : 'p -> 'p -> 'v)
      (a : 'p)
      (b : 'p)
      (c : 'p)
      (d : 'p) <=>
      ?centre : 'p. ?radius : real.
        q459547_dist inner vsub a centre = radius /\
        q459547_dist inner vsub b centre = radius /\
        q459547_dist inner vsub c centre = radius /\
        q459547_dist inner vsub d centre = radius``);

val q459547_ptolemy_s_theorem =
  ``!(zero : 'v)
      (add : 'v -> 'v -> 'v)
      (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v)
      (inner : 'v -> 'v -> real)
      (vadd : 'v -> 'p -> 'p)
      (vsub : 'p -> 'p -> 'v)
      (a b c d p : 'p).
      q459547_real_inner_affine_space
        zero add neg smul inner vadd vsub /\
      q459547_cospherical_four inner vsub a b c d /\
      q459547_angle inner vsub a p c = pi /\
      q459547_angle inner vsub b p d = pi
      ==>
      q459547_dist inner vsub a b *
          q459547_dist inner vsub c d +
        q459547_dist inner vsub b c *
          q459547_dist inner vsub d a =
        q459547_dist inner vsub a c *
          q459547_dist inner vsub b d``;

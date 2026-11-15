(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q2226868 (thousand-theorems__hol4__Q2226868), "Geometric mean theorem":
  in an arbitrary real inner-product affine space, the squared altitude of
  a right triangle equals the product of the two hypotenuse-segment lengths.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val q2226868_real_inner_affine_space_def = new_definition (
  "q2226868_real_inner_affine_space_def",
  ``q2226868_real_inner_affine_space
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

val q2226868_norm_def = new_definition (
  "q2226868_norm_def",
  ``q2226868_norm (inner : 'v -> 'v -> real) (x : 'v) =
      sqrt (inner x x)``);

val q2226868_dist_def = new_definition (
  "q2226868_dist_def",
  ``q2226868_dist
      (inner : 'v -> 'v -> real)
      (vsub : 'p -> 'p -> 'v)
      (p : 'p)
      (q : 'p) =
      q2226868_norm inner (vsub p q)``);

val q2226868_angle_def = new_definition (
  "q2226868_angle_def",
  ``q2226868_angle
      (inner : 'v -> 'v -> real)
      (vsub : 'p -> 'p -> 'v)
      (p : 'p)
      (q : 'p)
      (r : 'p) =
      acs
        (inner (vsub p q) (vsub r q) /
          (q2226868_norm inner (vsub p q) *
           q2226868_norm inner (vsub r q)))``);

val q2226868_strictly_between_def = new_definition (
  "q2226868_strictly_between_def",
  ``q2226868_strictly_between
      (smul : real -> 'v -> 'v)
      (vadd : 'v -> 'p -> 'p)
      (vsub : 'p -> 'p -> 'v)
      (p1 : 'p)
      (p4 : 'p)
      (p3 : 'p) <=>
      p1 <> p3 /\
      ?t : real.
        0 < t /\ t < 1 /\
        p4 = vadd (smul t (vsub p3 p1)) p1``);

val geometric_mean_theorem =
  ``!(zero : 'v)
      (add : 'v -> 'v -> 'v)
      (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v)
      (inner : 'v -> 'v -> real)
      (vadd : 'v -> 'p -> 'p)
      (vsub : 'p -> 'p -> 'v)
      (p1 p2 p3 p4 : 'p).
      q2226868_real_inner_affine_space
        zero add neg smul inner vadd vsub /\
      q2226868_strictly_between smul vadd vsub p1 p4 p3 /\
      q2226868_angle inner vsub p1 p4 p2 = pi / 2 /\
      q2226868_angle inner vsub p1 p2 p3 = pi / 2
      ==>
      q2226868_dist inner vsub p2 p4 pow 2 =
        q2226868_dist inner vsub p1 p4 *
          q2226868_dist inner vsub p3 p4``;

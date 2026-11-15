(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q5421989 (thousand-theorems__hol4__Q5421989), "Exterior angle theorem":
  if p1 lies strictly between p and p2 in a real inner-product affine space,
  then the exterior angle at p1 equals the sum of the two remote interior
  angles. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val q5421989_real_inner_affine_space_def = new_definition (
  "q5421989_real_inner_affine_space_def",
  ``q5421989_real_inner_affine_space
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

val q5421989_norm_def = new_definition (
  "q5421989_norm_def",
  ``q5421989_norm (inner : 'v -> 'v -> real) (x : 'v) =
      sqrt (inner x x)``);

val q5421989_angle_def = new_definition (
  "q5421989_angle_def",
  ``q5421989_angle
      (inner : 'v -> 'v -> real)
      (vsub : 'p -> 'p -> 'v)
      (p1 : 'p)
      (p2 : 'p)
      (p3 : 'p) =
      acs
        (inner (vsub p1 p2) (vsub p3 p2) /
          (q5421989_norm inner (vsub p1 p2) *
           q5421989_norm inner (vsub p3 p2)))``);

val q5421989_strictly_between_def = new_definition (
  "q5421989_strictly_between_def",
  ``q5421989_strictly_between
      (smul : real -> 'v -> 'v)
      (vadd : 'v -> 'p -> 'p)
      (vsub : 'p -> 'p -> 'v)
      (p : 'p)
      (p1 : 'p)
      (p2 : 'p) <=>
      p <> p2 /\
      ?r : real.
        0 < r /\ r < 1 /\
        p1 = vadd (smul r (vsub p2 p)) p``);

val exterior_angle_eq_angle_add_angle =
  ``!(zero : 'v)
      (add : 'v -> 'v -> 'v)
      (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v)
      (inner : 'v -> 'v -> real)
      (vadd : 'v -> 'p -> 'p)
      (vsub : 'p -> 'p -> 'v)
      (p p1 p2 p3 : 'p).
      q5421989_real_inner_affine_space
        zero add neg smul inner vadd vsub /\
      q5421989_strictly_between smul vadd vsub p p1 p2
      ==>
      q5421989_angle inner vsub p3 p1 p =
        q5421989_angle inner vsub p1 p3 p2 +
        q5421989_angle inner vsub p3 p2 p1``;

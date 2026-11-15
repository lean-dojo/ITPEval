(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q285719, "Thales's theorem": in an arbitrary real inner-product affine
  space, diameter endpoints subtend a right angle at exactly the points on
  the sphere, with the right-angle condition represented by equivalent
  inner-product orthogonality. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val q285719_real_inner_affine_space_def = new_definition (
  "q285719_real_inner_affine_space_def",
  ``q285719_real_inner_affine_space
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
      (!x y z. inner (add x y) z = inner x z + inner y z) /\
      (!r x y. inner (smul r x) y = r * inner x y) /\
      (!x y. inner x y = inner y x) /\
      (!x. 0 <= inner x x) /\
      (!x. (inner x x = 0 <=> x = zero)) /\
      (!p. vadd zero p = p) /\
      (!u v p. vadd (add u v) p = vadd u (vadd v p)) /\
      (!p q. vadd (vsub p q) q = p) /\
      (!v p. vsub (vadd v p) p = v)``);

val q285719_norm_def = new_definition (
  "q285719_norm_def",
  ``q285719_norm (inner : 'v -> 'v -> real) (x : 'v) =
      sqrt (inner x x)``);

val q285719_mem_sphere_def = new_definition (
  "q285719_mem_sphere_def",
  ``q285719_mem_sphere
      (inner : 'v -> 'v -> real)
      (vsub : 'p -> 'p -> 'v)
      (center : 'p)
      (radius : real)
      (p : 'p) <=>
      q285719_norm inner (vsub p center) = radius``);

val q285719_is_diameter_def = new_definition (
  "q285719_is_diameter_def",
  ``q285719_is_diameter
      (neg : 'v -> 'v)
      (inner : 'v -> 'v -> real)
      (vsub : 'p -> 'p -> 'v)
      (center : 'p)
      (radius : real)
      (p1 : 'p)
      (p3 : 'p) <=>
      q285719_mem_sphere inner vsub center radius p3 /\
      vsub p1 center = neg (vsub p3 center)``);

val thales_theorem =
  ``!(zero : 'v)
      (add : 'v -> 'v -> 'v)
      (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v)
      (inner : 'v -> 'v -> real)
      (vadd : 'v -> 'p -> 'p)
      (vsub : 'p -> 'p -> 'v)
      (center p1 p2 p3 : 'p)
      (radius : real).
      q285719_real_inner_affine_space
        zero add neg smul inner vadd vsub /\
      q285719_is_diameter neg inner vsub center radius p1 p3
      ==>
      (inner (vsub p1 p2) (vsub p3 p2) = 0 <=>
       q285719_mem_sphere inner vsub center radius p2)``;

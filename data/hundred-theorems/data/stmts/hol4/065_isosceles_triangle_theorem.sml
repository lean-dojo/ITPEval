(*
  Statement-only formalization of "Isosceles Triangle Theorem" from Hundred
  Theorems artifact 065: in any real inner-product space, equal lengths of the
  two sides meeting at the apex imply equality of the base angles, including
  degenerate triangles. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val isosceles_triangle_theorem =
  ``let is_real_inner_space =
      \(zero : 'a)
       (add : 'a -> 'a -> 'a)
       (neg : 'a -> 'a)
       (smul : real -> 'a -> 'a)
       (inner : 'a -> 'a -> real).
        (!x y z. add x (add y z) = add (add x y) z) /\
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
        (!x. (inner x x = 0 <=> x = zero))
    in
      !zero add neg smul inner.
        is_real_inner_space zero add neg smul inner
        ==>
        let sub = \x y. add x (neg y) in
        let norm = \x. sqrt (inner x x) in
        let dist = \P Q. norm (sub P Q) in
        let vector_angle =
          \u v.
            if u = zero \/ v = zero then
              pi / 2
            else
              acs (inner u v / (norm u * norm v))
        in
        let angle = \P Q R. vector_angle (sub P Q) (sub R Q) in
          !A B C.
            dist A C = dist B C
            ==>
            angle C A B = angle A B C``;

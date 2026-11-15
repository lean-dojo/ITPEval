(*
  Statement-only formalization of "Theorem of Ceva" from Hundred Theorems
  item 061: for a noncollinear triangle in the real coordinate plane, three
  concurrent cevians through points on the opposite side lines imply equality
  of the corresponding triple products of distances. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val theorem_of_ceva =
  ``!ax ay bx by cx cy xx xy yx yy zx zy px py : real.
      ~((ax - bx) * (cy - by) = (ay - by) * (cx - bx)) /\
      (bx - xx) * (cy - xy) = (by - xy) * (cx - xx) /\
      (cx - yx) * (ay - yy) = (cy - yy) * (ax - yx) /\
      (ax - zx) * (by - zy) = (ay - zy) * (bx - zx) /\
      (ax - px) * (xy - py) = (ay - py) * (xx - px) /\
      (bx - px) * (yy - py) = (by - py) * (yx - px) /\
      (cx - px) * (zy - py) = (cy - py) * (zx - px)
      ==>
      sqrt ((bx - xx) pow 2 + (by - xy) pow 2) *
        sqrt ((cx - yx) pow 2 + (cy - yy) pow 2) *
        sqrt ((ax - zx) pow 2 + (ay - zy) pow 2) =
      sqrt ((xx - cx) pow 2 + (xy - cy) pow 2) *
        sqrt ((yx - ax) pow 2 + (yy - ay) pow 2) *
        sqrt ((zx - bx) pow 2 + (zy - by) pow 2)``;

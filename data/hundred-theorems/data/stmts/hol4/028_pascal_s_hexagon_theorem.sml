(*
  Statement-only formalization of "Pascal's Hexagon Theorem" from Hundred Theorems item 028.
  This file contains no proof.
*)

(*
  Hundred Theorems item 028, "Pascal's Hexagon Theorem": six suitably nondegenerate affine
  points on a conic determine three collinear intersections of opposite sides. This is a
  statement-only formalization and contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory;

val pascals_hexagon_theorem =
  ``let collinear =
      \P Q R : real # real.
        (FST P - FST Q) * (SND R - SND Q) =
        (SND P - SND Q) * (FST R - FST Q)
    in
      !a b c d e f : real.
      !x1 x2 x3 x4 x5 x6 x7 x8 x9 : real # real.
        let on_conic =
          \P : real # real.
            a * ((FST P) pow 2) + b * ((SND P) pow 2) +
            c * FST P * SND P + d * FST P + e * SND P + f = 0
        in
          ~(a = 0 /\ b = 0 /\ c = 0 /\ d = 0 /\ e = 0 /\ f = 0) /\
          ~collinear x1 x2 x4 /\
          ~collinear x1 x2 x5 /\
          ~collinear x1 x2 x6 /\
          ~collinear x1 x3 x4 /\
          ~collinear x1 x3 x5 /\
          ~collinear x1 x3 x6 /\
          ~collinear x2 x3 x4 /\
          ~collinear x2 x3 x5 /\
          ~collinear x2 x3 x6 /\
          ~collinear x4 x5 x1 /\
          ~collinear x4 x5 x2 /\
          ~collinear x4 x5 x3 /\
          ~collinear x4 x6 x1 /\
          ~collinear x4 x6 x2 /\
          ~collinear x4 x6 x3 /\
          ~collinear x5 x6 x1 /\
          ~collinear x5 x6 x2 /\
          ~collinear x5 x6 x3
          ==>
          on_conic x1 /\ on_conic x2 /\ on_conic x3 /\
          on_conic x4 /\ on_conic x5 /\ on_conic x6 /\
          collinear x1 x9 x5 /\
          collinear x1 x8 x6 /\
          collinear x2 x9 x4 /\
          collinear x2 x7 x6 /\
          collinear x3 x8 x4 /\
          collinear x3 x7 x5
          ==>
          collinear x7 x8 x9``;

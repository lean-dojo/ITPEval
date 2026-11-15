(* Statement-only formalization of PutnamBench artifact putnam_1962_a3:
   a triangle's three cevian intersection points have the stated area ratio
   when the side-division ratios are equal. This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition point := (R * R)%type.

Definition affine_combination (t : R) (a b : point) : point :=
  ((1 - t) * fst a + t * fst b,
   (1 - t) * snd a + t * snd b).

Definition closed_segment (a b : point) : point -> Prop :=
  fun p =>
    exists t : R,
      0 <= t <= 1 /\
      p = affine_combination t a b.

Definition point_distance (a b : point) : R :=
  sqrt ((fst a - fst b) ^ 2 + (snd a - snd b) ^ 2).

Definition signed_twice_area (a b c : point) : R :=
  (fst b - fst a) * (snd c - snd a) -
  (snd b - snd a) * (fst c - fst a).

Definition noncollinear (a b c : point) : Prop :=
  signed_twice_area a b c <> 0.

Definition triangle_area (a b c : point) : R :=
  Rabs (signed_twice_area a b c) / 2.

Theorem putnam_1962_a3
    (A B C A' B' C' P Q Rpt : point)
    (k : R)
    (hk : k > 0)
    (hABC : noncollinear A B C)
    (hA' : closed_segment B C A' /\
           point_distance C A' / point_distance A' B = k)
    (hB' : closed_segment C A B' /\
           point_distance A B' / point_distance B' C = k)
    (hC' : closed_segment A B C' /\
           point_distance B C' / point_distance C' A = k)
    (hP : closed_segment B B' P /\ closed_segment C C' P)
    (hQ : closed_segment C C' Q /\ closed_segment A A' Q)
    (hR : closed_segment A A' Rpt /\ closed_segment B B' Rpt) :
  triangle_area P Q Rpt / triangle_area A B C =
  (k - 1) ^ 2 / (k ^ 2 + k + 1).
Admitted.

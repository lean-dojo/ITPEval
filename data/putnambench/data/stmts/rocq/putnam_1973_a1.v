(* Statement-only formalization of PutnamBench artifact putnam_1973_a1:
   the one-quarter area bound and the complementary-subtriangle area bound
   for points on the sides of a nondegenerate planar triangle. This file
   contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition point := (R * R)%type.

Definition affine_combination (t : R) (a b : point) : point :=
  ((1 - t) * fst a + t * fst b,
   (1 - t) * snd a + t * snd b).

Definition closed_segment (a b : point) : point -> Prop :=
  fun p : point =>
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

Theorem putnam_1973_a1
    (A B C X Y Z : point)
    (hABC : noncollinear A B C)
    (hX : closed_segment B C X)
    (hY : closed_segment C A Y)
    (hZ : closed_segment A B Z) :
  ((point_distance B X <= point_distance X C /\
    point_distance C Y <= point_distance Y A /\
    point_distance A Z <= point_distance Z B) ->
   triangle_area X Y Z >=
     (1 / 4) * triangle_area A B C) /\
  Rmin
    (triangle_area A Z Y)
    (Rmin (triangle_area B X Z) (triangle_area C Y X))
    <= triangle_area X Y Z.
Admitted.

(* Statement-only formalization of PutnamBench artifact putnam_1965_a1:
   a planar triangle with two specified external-angle bisector intersections
   and equal-length constraints has angle CAB equal to pi/15.
   This file contains no proof. *)

From Stdlib Require Import Reals Rtrigo1.

Open Scope R_scope.

Definition point := (R * R)%type.

Definition point_sub (a b : point) : point :=
  (fst a - fst b, snd a - snd b).

Definition point_dot (u v : point) : R :=
  fst u * fst v + snd u * snd v.

Definition point_norm (u : point) : R :=
  sqrt (fst u ^ 2 + snd u ^ 2).

Definition point_distance (a b : point) : R :=
  point_norm (point_sub a b).

Definition vector_is_zero (u : point) : bool :=
  if Req_EM_T (fst u) 0 then
    if Req_EM_T (snd u) 0 then true else false
  else false.

Definition real_arccos (x : R) : R :=
  if Rle_dec x (-1) then PI
  else if Rle_dec 1 x then 0
  else PI / 2 - atan (x / sqrt (1 - x ^ 2)).

Definition vector_angle (u v : point) : R :=
  if orb (vector_is_zero u) (vector_is_zero v) then PI / 2
  else real_arccos (point_dot u v / (point_norm u * point_norm v)).

Definition angle (a b c : point) : R :=
  vector_angle (point_sub a b) (point_sub c b).

Definition collinear_points (a b c : point) : Prop :=
  (fst b - fst a) * (snd c - snd a) =
  (snd b - snd a) * (fst c - fst a).

Definition putnam_1965_a1_solution : R := PI / 15.

Theorem putnam_1965_a1
    (A B C X Y : point)
    (hABC : ~ collinear_points A B C)
    (hangles :
      angle C A B < angle B C A /\
      angle B C A < PI / 2 /\
      PI / 2 < angle A B C)
    (hX :
      collinear_points X B C /\
      angle X A B = (PI - angle C A B) / 2 /\
      point_distance A X = point_distance A B)
    (hY :
      collinear_points Y C A /\
      angle Y B C = (PI - angle A B C) / 2 /\
      point_distance B Y = point_distance A B) :
  angle C A B = putnam_1965_a1_solution.
Admitted.

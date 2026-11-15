(* Statement-only formalization of PutnamBench corpus artifact putnam_2016_b3:
   a finite planar point set whose every three-point triangle has area at most
   one is contained in a triangle of area four. This file contains no proof. *)

From Stdlib Require Import Reals Ensembles Finite_sets.

Open Scope R_scope.

Definition putnam_2016_b3_point : Type := (R * R)%type.
Definition putnam_2016_b3_point_set :=
  putnam_2016_b3_point -> Prop.

Definition putnam_2016_b3_triangle_area
    (A B C : putnam_2016_b3_point) : R :=
  Rabs
    ((fst B - fst A) * (snd C - snd A) -
     (snd B - snd A) * (fst C - fst A)) / 2.

Definition putnam_2016_b3_in_triangle
    (A B C P : putnam_2016_b3_point) : Prop :=
  exists alpha beta gamma : R,
    0 <= alpha /\
    0 <= beta /\
    0 <= gamma /\
    alpha + beta + gamma = 1 /\
    fst P = alpha * fst A + beta * fst B + gamma * fst C /\
    snd P = alpha * snd A + beta * snd B + gamma * snd C.

Theorem putnam_2016_b3
    (S : putnam_2016_b3_point_set)
    (hS_finite : Finite putnam_2016_b3_point S)
    (hS_area :
      forall A B C : putnam_2016_b3_point,
        S A ->
        S B ->
        S C ->
        putnam_2016_b3_triangle_area A B C <= 1) :
  exists A' B' C' : putnam_2016_b3_point,
    putnam_2016_b3_triangle_area A' B' C' = 4 /\
    forall P : putnam_2016_b3_point,
      S P ->
      putnam_2016_b3_in_triangle A' B' C' P.
Admitted.

(* Statement-only formalization of PutnamBench corpus artifact putnam_1994_a3:
   a four-coloring of the closed unit isosceles right triangle has two
   same-colored points at distance at least 2 minus sqrt 2.
   This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition putnam_1994_a3_point : Type := (R * R)%type.

Inductive putnam_1994_a3_color : Type :=
| putnam_1994_a3_color0
| putnam_1994_a3_color1
| putnam_1994_a3_color2
| putnam_1994_a3_color3.

Definition putnam_1994_a3_in_triangle
    (p : putnam_1994_a3_point) : Prop :=
  0 <= fst p /\
  0 <= snd p /\
  fst p + snd p <= 1.

Definition putnam_1994_a3_distance
    (p q : putnam_1994_a3_point) : R :=
  sqrt ((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2).

Theorem putnam_1994_a3
    (T : putnam_1994_a3_point -> Prop)
    (T_def :
      forall p : putnam_1994_a3_point,
        T p <-> putnam_1994_a3_in_triangle p)
    (Tcolors : putnam_1994_a3_point -> putnam_1994_a3_color) :
  exists p q : putnam_1994_a3_point,
    T p /\
    T q /\
    Tcolors p = Tcolors q /\
    2 - sqrt 2 <= putnam_1994_a3_distance p q.
Admitted.

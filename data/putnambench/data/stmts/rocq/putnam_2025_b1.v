(* Statement-only formalization of PutnamBench corpus artifact putnam_2025_b1:
   a two-coloring of the real plane closed under circumcenters of monochromatic
   noncollinear triples is constant. This file contains no proof. *)

From Stdlib Require Import Reals Bool.Bool.

Open Scope R_scope.

Definition putnam_2025_b1_point : Type := (R * R)%type.

Definition putnam_2025_b1_noncollinear
    (A B C : putnam_2025_b1_point) : Prop :=
  (fst B - fst A) * (snd C - snd A) -
  (snd B - snd A) * (fst C - fst A) <> 0.

Definition putnam_2025_b1_squared_distance
    (P Q : putnam_2025_b1_point) : R :=
  (fst P - fst Q) ^ 2 + (snd P - snd Q) ^ 2.

Definition putnam_2025_b1_is_circumcenter
    (A B C O : putnam_2025_b1_point) : Prop :=
  putnam_2025_b1_squared_distance O A =
    putnam_2025_b1_squared_distance O B /\
  putnam_2025_b1_squared_distance O A =
    putnam_2025_b1_squared_distance O C.

Theorem putnam_2025_b1
    (color : putnam_2025_b1_point -> bool)
    (h :
      forall A B C : putnam_2025_b1_point,
        putnam_2025_b1_noncollinear A B C ->
        color A = color B ->
        color A = color C ->
        forall O : putnam_2025_b1_point,
          putnam_2025_b1_is_circumcenter A B C O ->
          color O = color A) :
  exists c : bool,
    forall P : putnam_2025_b1_point, color P = c.
Admitted.

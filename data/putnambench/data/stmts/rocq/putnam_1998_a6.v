(* Statement-only formalization of PutnamBench corpus artifact putnam_1998_a6:
   three distinct lattice points in the Euclidean plane satisfying the stated
   two-side-length and triangle-area inequality form three vertices of a
   square. This file contains no proof. *)

From Stdlib Require Import Reals ZArith.

Open Scope R_scope.

Definition putnam_1998_a6_point : Type := (R * R)%type.

Definition putnam_1998_a6_subtract
    (p q : putnam_1998_a6_point) : putnam_1998_a6_point :=
  (fst p - fst q, snd p - snd q).

Definition putnam_1998_a6_dot
    (p q : putnam_1998_a6_point) : R :=
  fst p * fst q + snd p * snd q.

Definition putnam_1998_a6_distance
    (p q : putnam_1998_a6_point) : R :=
  sqrt ((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2).

Definition putnam_1998_a6_triangle_area
    (a b c : putnam_1998_a6_point) : R :=
  Rabs
    ((fst b - fst a) * (snd c - snd a) -
     (snd b - snd a) * (fst c - fst a)) / 2.

Definition putnam_1998_a6_lattice_point
    (p : putnam_1998_a6_point) : Prop :=
  exists x y : Z, p = (IZR x, IZR y).

Definition putnam_1998_a6_three_square
    (p q r : putnam_1998_a6_point) : Prop :=
  putnam_1998_a6_distance q p = putnam_1998_a6_distance q r /\
  putnam_1998_a6_dot
    (putnam_1998_a6_subtract p q)
    (putnam_1998_a6_subtract r q) = 0.

Theorem putnam_1998_a6
    (A B C : putnam_1998_a6_point)
    (hinteger :
      putnam_1998_a6_lattice_point A /\
      putnam_1998_a6_lattice_point B /\
      putnam_1998_a6_lattice_point C)
    (hdistinct : A <> B /\ A <> C /\ B <> C)
    (harea :
      (putnam_1998_a6_distance A B +
       putnam_1998_a6_distance B C) ^ 2 <
      8 * putnam_1998_a6_triangle_area A B C + 1) :
  putnam_1998_a6_three_square A B C \/
  putnam_1998_a6_three_square B C A \/
  putnam_1998_a6_three_square C A B.
Admitted.

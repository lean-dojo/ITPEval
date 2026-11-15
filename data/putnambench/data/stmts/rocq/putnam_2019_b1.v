(* Statement-only formalization of PutnamBench corpus artifact putnam_2019_b1:
   the number of four-point subsets of specified integer-coordinate circles
   whose points are the vertices of a square. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat ZArith Ensembles Finite_sets.

Local Open Scope Z_scope.

Definition putnam_2019_b1_point : Type := (Z * Z)%type.

Definition putnam_2019_b1_x (p : putnam_2019_b1_point) : Z := fst p.

Definition putnam_2019_b1_y (p : putnam_2019_b1_point) : Z := snd p.

Definition putnam_2019_b1_point_lt
    (p q : putnam_2019_b1_point) : Prop :=
  Z.lt (putnam_2019_b1_x p) (putnam_2019_b1_x q) \/
  (putnam_2019_b1_x p = putnam_2019_b1_x q /\
   Z.lt (putnam_2019_b1_y p) (putnam_2019_b1_y q)).

Definition putnam_2019_b1_Pn
    (n : nat) (p : putnam_2019_b1_point) : Prop :=
  p = (0%Z, 0%Z) \/
  exists k : nat,
    Nat.le k n /\
    Z.pow (putnam_2019_b1_x p) 2 +
      Z.pow (putnam_2019_b1_y p) 2 = Z.pow 2 (Z.of_nat k).

Record putnam_2019_b1_four_points : Type := {
  putnam_2019_b1_p0 : putnam_2019_b1_point;
  putnam_2019_b1_p1 : putnam_2019_b1_point;
  putnam_2019_b1_p2 : putnam_2019_b1_point;
  putnam_2019_b1_p3 : putnam_2019_b1_point
}.

Definition putnam_2019_b1_sorted
    (q : putnam_2019_b1_four_points) : Prop :=
  putnam_2019_b1_point_lt
    (putnam_2019_b1_p0 q) (putnam_2019_b1_p1 q) /\
  putnam_2019_b1_point_lt
    (putnam_2019_b1_p1 q) (putnam_2019_b1_p2 q) /\
  putnam_2019_b1_point_lt
    (putnam_2019_b1_p2 q) (putnam_2019_b1_p3 q).

Definition putnam_2019_b1_squared_distance
    (p q : putnam_2019_b1_point) : Z :=
  Z.pow (putnam_2019_b1_x p - putnam_2019_b1_x q) 2 +
  Z.pow (putnam_2019_b1_y p - putnam_2019_b1_y q) 2.

Definition putnam_2019_b1_same_four_points
    (q : putnam_2019_b1_four_points)
    (a b c d : putnam_2019_b1_point) : Prop :=
  forall p : putnam_2019_b1_point,
    (p = a \/ p = b \/ p = c \/ p = d) <->
    (p = putnam_2019_b1_p0 q \/
     p = putnam_2019_b1_p1 q \/
     p = putnam_2019_b1_p2 q \/
     p = putnam_2019_b1_p3 q).

Definition putnam_2019_b1_is_square
    (q : putnam_2019_b1_four_points) : Prop :=
  exists a b c d : putnam_2019_b1_point,
    putnam_2019_b1_same_four_points q a b c d /\
    putnam_2019_b1_squared_distance a b <> 0%Z /\
    putnam_2019_b1_squared_distance a b =
      putnam_2019_b1_squared_distance b c /\
    putnam_2019_b1_squared_distance b c =
      putnam_2019_b1_squared_distance c d /\
    putnam_2019_b1_squared_distance c d =
      putnam_2019_b1_squared_distance d a /\
    putnam_2019_b1_squared_distance a c =
      putnam_2019_b1_squared_distance b d.

Definition putnam_2019_b1_square_subsets
    (n : nat) : Ensemble putnam_2019_b1_four_points :=
  fun q : putnam_2019_b1_four_points =>
    putnam_2019_b1_sorted q /\
    putnam_2019_b1_Pn n (putnam_2019_b1_p0 q) /\
    putnam_2019_b1_Pn n (putnam_2019_b1_p1 q) /\
    putnam_2019_b1_Pn n (putnam_2019_b1_p2 q) /\
    putnam_2019_b1_Pn n (putnam_2019_b1_p3 q) /\
    putnam_2019_b1_is_square q.

Definition putnam_2019_b1_solution (n : nat) : nat :=
  (5 * n + 1)%nat.

Theorem putnam_2019_b1 (n : nat) :
  cardinal putnam_2019_b1_four_points
    (putnam_2019_b1_square_subsets n)
    (putnam_2019_b1_solution n).
Admitted.

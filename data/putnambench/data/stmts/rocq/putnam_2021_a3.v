(* Statement-only formalization of PutnamBench corpus artifact putnam_2021_a3:
   the positive integers N for which the sphere x^2 + y^2 + z^2 = N
   contains an inscribed regular tetrahedron with integer-coordinate vertices.
   This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat ZArith.ZArith.

Open Scope Z_scope.

Definition putnam_2021_a3_point : Type := (Z * (Z * Z))%type.

Definition putnam_2021_a3_x (p : putnam_2021_a3_point) : Z :=
  fst p.

Definition putnam_2021_a3_y (p : putnam_2021_a3_point) : Z :=
  fst (snd p).

Definition putnam_2021_a3_z (p : putnam_2021_a3_point) : Z :=
  snd (snd p).

Definition putnam_2021_a3_sqnorm
    (p : putnam_2021_a3_point) : Z :=
  putnam_2021_a3_x p ^ 2 +
  putnam_2021_a3_y p ^ 2 +
  putnam_2021_a3_z p ^ 2.

Definition putnam_2021_a3_on_sphere
    (N : nat) (p : putnam_2021_a3_point) : Prop :=
  putnam_2021_a3_sqnorm p = Z.of_nat N.

Definition putnam_2021_a3_sqdist
    (p q : putnam_2021_a3_point) : Z :=
  (putnam_2021_a3_x p - putnam_2021_a3_x q) ^ 2 +
  (putnam_2021_a3_y p - putnam_2021_a3_y q) ^ 2 +
  (putnam_2021_a3_z p - putnam_2021_a3_z q) ^ 2.

Definition putnam_2021_a3_regular
    (A B C D : putnam_2021_a3_point) : Prop :=
  0 < putnam_2021_a3_sqdist A B /\
  putnam_2021_a3_sqdist A C = putnam_2021_a3_sqdist A B /\
  putnam_2021_a3_sqdist A D = putnam_2021_a3_sqdist A B /\
  putnam_2021_a3_sqdist B C = putnam_2021_a3_sqdist A B /\
  putnam_2021_a3_sqdist B D = putnam_2021_a3_sqdist A B /\
  putnam_2021_a3_sqdist C D = putnam_2021_a3_sqdist A B.

Definition putnam_2021_a3_has_tetrahedron (N : nat) : Prop :=
  exists A B C D : putnam_2021_a3_point,
    putnam_2021_a3_on_sphere N A /\
    putnam_2021_a3_on_sphere N B /\
    putnam_2021_a3_on_sphere N C /\
    putnam_2021_a3_on_sphere N D /\
    putnam_2021_a3_regular A B C D.

Definition putnam_2021_a3_solution (N : nat) : Prop :=
  exists m : nat,
    (0 < m)%nat /\
    N = (3 * m ^ 2)%nat.

Theorem putnam_2021_a3 :
  forall N : nat,
    ((0 < N)%nat /\ putnam_2021_a3_has_tetrahedron N) <->
    putnam_2021_a3_solution N.
Admitted.

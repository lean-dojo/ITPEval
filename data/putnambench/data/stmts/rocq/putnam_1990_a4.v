(* Statement-only formalization of PutnamBench artifact putnam_1990_a4:
   the least number of paper-punch centers whose irrational-distance loci
   cover the real Euclidean plane is three; this file contains no proof. *)

From Stdlib Require Import Reals QArith Lists.List.

Open Scope R_scope.

Definition putnam_1990_a4_point : Type :=
  (R * R)%type.

Definition putnam_1990_a4_distance
    (p q : putnam_1990_a4_point) : R :=
  sqrt ((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2).

Definition putnam_1990_a4_irrational (x : R) : Prop :=
  ~ exists q : Q, x = Q2R q.

Definition putnam_1990_a4_feasible (n : nat) : Prop :=
  exists centers : list putnam_1990_a4_point,
    NoDup centers /\
    length centers = n /\
    forall q : putnam_1990_a4_point,
      exists p : putnam_1990_a4_point,
        In p centers /\
        putnam_1990_a4_irrational
          (putnam_1990_a4_distance p q).

Definition putnam_1990_a4_solution : nat :=
  3%nat.

Theorem putnam_1990_a4 :
  putnam_1990_a4_feasible putnam_1990_a4_solution /\
  forall n : nat,
    putnam_1990_a4_feasible n ->
    (putnam_1990_a4_solution <= n)%nat.
Admitted.

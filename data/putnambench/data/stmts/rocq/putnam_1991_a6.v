(* Statement-only formalization of PutnamBench artifact putnam_1991_a6:
   equality between counts of constrained positive-integer compositions and
   nonincreasing compositions using an inhomogeneous Fibonacci sequence.
   This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List.

Definition putnam_1991_a6_has_cardinality
    {X : Type} (P : X -> Prop) (cardinality : nat) : Prop :=
  exists enumeration : list X,
    NoDup enumeration /\
    length enumeration = cardinality /\
    forall x : X, In x enumeration <-> P x.

Definition putnam_1991_a6_composition
    (n : nat) (terms : list nat) : Prop :=
  terms <> nil /\
  Forall (fun term : nat => 0 < term) terms /\
  fold_right Nat.add 0 terms = n.

Definition putnam_1991_a6_agt (terms : list nat) : Prop :=
  (forall i : nat,
      i + 2 < length terms ->
      nth i terms 0 >
        nth (i + 1) terms 0 + nth (i + 2) terms 0) /\
  (1 < length terms ->
    nth (length terms - 2) terms 0 >
      nth (length terms - 1) terms 0).

Definition putnam_1991_a6_bge (terms : list nat) : Prop :=
  forall i : nat,
    i + 1 < length terms ->
    nth i terms 0 >= nth (i + 1) terms 0.

Definition putnam_1991_a6_bg1
    (g : nat -> nat) (terms : list nat) : Prop :=
  forall term : nat,
    In term terms ->
    exists j : nat, term = g j.

Definition putnam_1991_a6_bg2
    (g : nat -> nat) (terms : list nat) : Prop :=
  exists k : nat,
    nth 0 terms 0 = g k /\
    forall j : nat,
      j <= k ->
      In (g j) terms.

Definition putnam_1991_a6_A_member
    (n : nat) (terms : list nat) : Prop :=
  putnam_1991_a6_composition n terms /\
  putnam_1991_a6_agt terms.

Definition putnam_1991_a6_B_member
    (g : nat -> nat) (n : nat) (terms : list nat) : Prop :=
  putnam_1991_a6_composition n terms /\
  putnam_1991_a6_bge terms /\
  putnam_1991_a6_bg1 g terms /\
  putnam_1991_a6_bg2 g terms.

Definition putnam_1991_a6_recurrence (g : nat -> nat) : Prop :=
  g 0 = 1 /\
  g 1 = 2 /\
  forall j : nat,
    2 <= j ->
    g j = g (j - 1) + g (j - 2) + 1.

Theorem putnam_1991_a6 :
  forall A g B : nat -> nat,
    putnam_1991_a6_recurrence g ->
    (forall n : nat,
        1 <= n ->
        putnam_1991_a6_has_cardinality
          (putnam_1991_a6_A_member n) (A n)) ->
    (forall n : nat,
        1 <= n ->
        putnam_1991_a6_has_cardinality
          (putnam_1991_a6_B_member g n) (B n)) ->
    forall n : nat, 1 <= n -> A n = B n.
Admitted.

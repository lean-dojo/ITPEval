(* Statement-only formalization of PutnamBench artifact putnam_1977_b3:
   eventual balancing of positive irrational real triples under a piecewise
   doubling map, with the answer that this does not always occur; this file
   contains no proof. *)

From Stdlib Require Import Reals QArith.

Open Scope R_scope.

Definition putnam_1977_b3_triple : Type :=
  (R * R * R)%type.

Definition putnam_1977_b3_irrational (x : R) : Prop :=
  ~ exists q : Q, x = Q2R q.

Definition putnam_1977_b3_positive_irrational
    (t : putnam_1977_b3_triple) : Prop :=
  let '(a, b, c) := t in
  putnam_1977_b3_irrational a /\
  putnam_1977_b3_irrational b /\
  putnam_1977_b3_irrational c /\
  a > 0 /\
  b > 0 /\
  c > 0 /\
  a + b + c = 1.

Definition putnam_1977_b3_balanced
    (t : putnam_1977_b3_triple) : Prop :=
  let '(a, b, c) := t in
  a < 1 / 2 /\ b < 1 / 2 /\ c < 1 / 2.

Definition putnam_1977_b3_step_coordinate (x : R) : R :=
  if Rlt_dec (1 / 2) x then 2 * x - 1 else 2 * x.

Definition putnam_1977_b3_balancing_act
    (t : putnam_1977_b3_triple) : putnam_1977_b3_triple :=
  let '(a, b, c) := t in
  (putnam_1977_b3_step_coordinate a,
   putnam_1977_b3_step_coordinate b,
   putnam_1977_b3_step_coordinate c).

Fixpoint putnam_1977_b3_iterate
    (B : putnam_1977_b3_triple -> putnam_1977_b3_triple)
    (n : nat)
    (t : putnam_1977_b3_triple) : putnam_1977_b3_triple :=
  match n with
  | O => t
  | S k => B (putnam_1977_b3_iterate B k t)
  end.

Definition putnam_1977_b3_solution : Prop := False.

Theorem putnam_1977_b3
    (P balanced : putnam_1977_b3_triple -> Prop)
    (B : putnam_1977_b3_triple -> putnam_1977_b3_triple)
    (hP : P = putnam_1977_b3_positive_irrational)
    (hbalanced : balanced = putnam_1977_b3_balanced)
    (hB : B = putnam_1977_b3_balancing_act) :
  (forall t : putnam_1977_b3_triple,
      P t ->
      exists n : nat,
        balanced (putnam_1977_b3_iterate B n t)) <->
  putnam_1977_b3_solution.
Admitted.

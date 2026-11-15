(* Statement-only formalization of PutnamBench corpus artifact putnam_2023_b1:
   the number of coin configurations reachable by diagonal legal moves on an
   m-by-n grid is a binomial coefficient. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Bool.Bool.

Import ListNotations.

Definition putnam_2023_b1_configuration : Type :=
  nat -> nat -> bool.

Definition putnam_2023_b1_initial
    (m n : nat) : putnam_2023_b1_configuration :=
  fun i j =>
    andb (Nat.ltb i (m - 1)) (Nat.ltb j (n - 1)).

Definition putnam_2023_b1_same_configuration
    (coins1 coins2 : putnam_2023_b1_configuration) : Prop :=
  forall i j : nat, coins1 i j = coins2 i j.

Definition putnam_2023_b1_legal_move
    (m n : nat)
    (coins1 coins2 : putnam_2023_b1_configuration) : Prop :=
  exists i j : nat,
    (i < m - 1)%nat /\
    (j < n - 1)%nat /\
    coins1 i j = true /\
    coins1 (S i) j = false /\
    coins1 i (S j) = false /\
    coins1 (S i) (S j) = false /\
    coins2 i j = false /\
    coins2 (S i) j = false /\
    coins2 i (S j) = false /\
    coins2 (S i) (S j) = true /\
    forall i' j' : nat,
      (i', j') <> (i, j) ->
      (i', j') <> (S i, j) ->
      (i', j') <> (i, S j) ->
      (i', j') <> (S i, S j) ->
      coins1 i' j' = coins2 i' j'.

Fixpoint putnam_2023_b1_legal_transitions
    (m n : nat)
    (previous : putnam_2023_b1_configuration)
    (remaining : list putnam_2023_b1_configuration) : Prop :=
  match remaining with
  | [] => True
  | current :: rest =>
      putnam_2023_b1_legal_move m n previous current /\
      putnam_2023_b1_legal_transitions m n current rest
  end.

Definition putnam_2023_b1_legal_sequence
    (m n : nat)
    (sequence : list putnam_2023_b1_configuration) : Prop :=
  exists rest : list putnam_2023_b1_configuration,
    sequence = putnam_2023_b1_initial m n :: rest /\
    putnam_2023_b1_legal_transitions
      m n (putnam_2023_b1_initial m n) rest.

Definition putnam_2023_b1_reachable
    (m n : nat)
    (config : putnam_2023_b1_configuration) : Prop :=
  exists sequence : list putnam_2023_b1_configuration,
    putnam_2023_b1_legal_sequence m n sequence /\
    putnam_2023_b1_same_configuration
      config (last sequence (putnam_2023_b1_initial m n)).

Fixpoint putnam_2023_b1_no_duplicate_configurations
    (configurations : list putnam_2023_b1_configuration) : Prop :=
  match configurations with
  | [] => True
  | config :: rest =>
      (forall other : putnam_2023_b1_configuration,
        In other rest ->
        ~ putnam_2023_b1_same_configuration config other) /\
      putnam_2023_b1_no_duplicate_configurations rest
  end.

Definition putnam_2023_b1_has_cardinality
    (P : putnam_2023_b1_configuration -> Prop)
    (cardinality : nat) : Prop :=
  exists enumeration : list putnam_2023_b1_configuration,
    putnam_2023_b1_no_duplicate_configurations enumeration /\
    length enumeration = cardinality /\
    forall config : putnam_2023_b1_configuration,
      P config <->
      exists representative : putnam_2023_b1_configuration,
        In representative enumeration /\
        putnam_2023_b1_same_configuration config representative.

Fixpoint putnam_2023_b1_binomial (n k : nat) : nat :=
  match n, k with
  | _, O => 1
  | O, S _ => 0
  | S n', S k' =>
      putnam_2023_b1_binomial n' k' +
      putnam_2023_b1_binomial n' (S k')
  end.

Definition putnam_2023_b1_solution (m n : nat) : nat :=
  putnam_2023_b1_binomial (m + n - 2) (m - 1).

Theorem putnam_2023_b1 :
  forall m n : nat,
    (0 < m)%nat ->
    (0 < n)%nat ->
    putnam_2023_b1_has_cardinality
      (putnam_2023_b1_reachable m n)
      (putnam_2023_b1_solution m n).
Admitted.

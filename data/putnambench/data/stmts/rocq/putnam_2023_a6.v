(* Statement-only formalization of PutnamBench corpus artifact putnam_2023_a6:
   Bob has a winning parity strategy in the alternating permutation game for
   every positive number of choices. This file contains no proof. *)

From Coq Require Import Arith.PeanoNat Lists.List.

Definition putnam_2023_a6_valid_game (n : nat) (g : list nat) : Prop :=
  length g = n /\
  NoDup g /\
  forall x : nat, In x g -> (1 <= x <= n)%nat.

Definition putnam_2023_a6_valid_partial_game
    (n : nat) (g : list nat) : Prop :=
  (length g <= n)%nat /\
  NoDup g /\
  forall x : nat, In x g -> (1 <= x <= n)%nat.

Definition putnam_2023_a6_fixed_at (g : list nat) (i : nat) : bool :=
  match nth_error g i with
  | Some x => Nat.eqb x (S i)
  | None => false
  end.

Definition putnam_2023_a6_parity (g : list nat) : nat :=
  (length
     (filter
        (putnam_2023_a6_fixed_at g)
        (seq 0 (length g)))) mod 2.

Definition putnam_2023_a6_conforms
    (g : list nat) (strategy : list nat -> nat) : Prop :=
  forall i : nat,
    (i < length g)%nat ->
    Nat.Odd i ->
    nth_error g i = Some (strategy (firstn i g)).

Definition putnam_2023_a6_valid_strategy
    (n : nat) (strategy : list nat -> nat) : Prop :=
  forall g : list nat,
    putnam_2023_a6_valid_partial_game n g ->
    (length g < n)%nat ->
    Nat.Odd (length g) ->
    (1 <= strategy g <= n)%nat /\
    ~ In (strategy g) g.

Definition putnam_2023_a6_winning_strategy
    (n : nat) (strategy : list nat -> nat) : Prop :=
  putnam_2023_a6_valid_strategy n strategy /\
  exists goal : nat,
    (goal < 2)%nat /\
    forall g : list nat,
      putnam_2023_a6_valid_game n g ->
      putnam_2023_a6_conforms g strategy ->
      putnam_2023_a6_parity g = goal.

Definition putnam_2023_a6_solution (n : nat) : Prop :=
  (0 < n)%nat.

Theorem putnam_2023_a6 :
  forall n : nat,
    ((0 < n)%nat /\
     exists strategy : list nat -> nat,
       putnam_2023_a6_winning_strategy n strategy) <->
    putnam_2023_a6_solution n.
Admitted.

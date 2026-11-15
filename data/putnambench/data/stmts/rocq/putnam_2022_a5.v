(* Statement-only formalization of PutnamBench corpus artifact putnam_2022_a5:
   the greatest number of uncovered squares Alice can guarantee in the
   alternating adjacent-domino game on a row of 2022 squares is 290.
   This file contains no proof. *)

From Stdlib Require Import Lists.List Vectors.Fin Arith.PeanoNat.

Import ListNotations.

Definition putnam_2022_a5_square : Type := Fin.t 2022.
Definition putnam_2022_a5_board : Type :=
  putnam_2022_a5_square -> Prop.

Definition putnam_2022_a5_same_board
    (left right : putnam_2022_a5_board) : Prop :=
  forall square : putnam_2022_a5_square,
    left square <-> right square.

Definition putnam_2022_a5_index
    (square : putnam_2022_a5_square) : nat :=
  proj1_sig (Fin.to_nat square).

Definition putnam_2022_a5_right_neighbor
    (left right : putnam_2022_a5_square) : Prop :=
  (putnam_2022_a5_index left < 2021)%nat /\
  putnam_2022_a5_index right =
    S (putnam_2022_a5_index left).

Definition putnam_2022_a5_empty_board :
    putnam_2022_a5_board :=
  fun _ => False.

Definition putnam_2022_a5_add_domino
    (board : putnam_2022_a5_board)
    (left right : putnam_2022_a5_square) :
    putnam_2022_a5_board :=
  fun square =>
    board square \/ square = left \/ square = right.

Definition putnam_2022_a5_terminal
    (board : putnam_2022_a5_board) : Prop :=
  forall left right : putnam_2022_a5_square,
    putnam_2022_a5_right_neighbor left right ->
    ~ board left ->
    board right.

Definition putnam_2022_a5_places_domino
    (before after : putnam_2022_a5_board) : Prop :=
  exists left right : putnam_2022_a5_square,
    putnam_2022_a5_right_neighbor left right /\
    ~ before left /\
    ~ before right /\
    putnam_2022_a5_same_board after
      (putnam_2022_a5_add_domino before left right).

Definition putnam_2022_a5_valid_move
    (before after : putnam_2022_a5_board) : Prop :=
  (putnam_2022_a5_same_board before after /\
   putnam_2022_a5_terminal before) \/
  putnam_2022_a5_places_domino before after.

Fixpoint putnam_2022_a5_chain_from
    (before : putnam_2022_a5_board)
    (rest : list putnam_2022_a5_board) : Prop :=
  match rest with
  | [] => True
  | after :: tail =>
      putnam_2022_a5_valid_move before after /\
      putnam_2022_a5_chain_from after tail
  end.

Definition putnam_2022_a5_chain
    (game : list putnam_2022_a5_board) : Prop :=
  match game with
  | [] => True
  | first :: rest => putnam_2022_a5_chain_from first rest
  end.

Definition putnam_2022_a5_starts_empty
    (game : list putnam_2022_a5_board) : Prop :=
  match game with
  | [] => False
  | first :: _ =>
      putnam_2022_a5_same_board
        first putnam_2022_a5_empty_board
  end.

Definition putnam_2022_a5_valid_game
    (game : list putnam_2022_a5_board) : Prop :=
  putnam_2022_a5_starts_empty game /\
  putnam_2022_a5_chain game.

Definition putnam_2022_a5_strategy : Type :=
  putnam_2022_a5_board -> putnam_2022_a5_board.

Definition putnam_2022_a5_conforms_to_strategy
    (game : list putnam_2022_a5_board)
    (strategy : putnam_2022_a5_strategy) : Prop :=
  forall (index : nat)
      (before after : putnam_2022_a5_board),
    nth_error game index = Some before ->
    nth_error game (S index) = Some after ->
    Nat.Even index ->
    putnam_2022_a5_same_board after (strategy before).

Inductive putnam_2022_a5_last_state :
    list putnam_2022_a5_board ->
    putnam_2022_a5_board ->
    Prop :=
  | putnam_2022_a5_last_singleton :
      forall board : putnam_2022_a5_board,
        putnam_2022_a5_last_state [board] board
  | putnam_2022_a5_last_cons :
      forall (first final : putnam_2022_a5_board)
          (rest : list putnam_2022_a5_board),
        putnam_2022_a5_last_state rest final ->
        putnam_2022_a5_last_state (first :: rest) final.

Definition putnam_2022_a5_uncovered_at_least
    (board : putnam_2022_a5_board)
    (lower_bound : nat) : Prop :=
  exists uncovered : list putnam_2022_a5_square,
    NoDup uncovered /\
    (forall square : putnam_2022_a5_square,
      In square uncovered <-> ~ board square) /\
    (lower_bound <= length uncovered)%nat.

Definition putnam_2022_a5_can_ensure
    (lower_bound : nat) : Prop :=
  exists strategy : putnam_2022_a5_strategy,
    (forall board : putnam_2022_a5_board,
      putnam_2022_a5_valid_move board (strategy board)) /\
    forall game : list putnam_2022_a5_board,
      putnam_2022_a5_valid_game game ->
      putnam_2022_a5_conforms_to_strategy game strategy ->
      exists final : putnam_2022_a5_board,
        putnam_2022_a5_last_state game final /\
        putnam_2022_a5_uncovered_at_least final lower_bound.

Definition putnam_2022_a5_solution : nat := 290.

Theorem putnam_2022_a5 :
  putnam_2022_a5_can_ensure putnam_2022_a5_solution /\
  forall lower_bound : nat,
    putnam_2022_a5_can_ensure lower_bound ->
    (lower_bound <= putnam_2022_a5_solution)%nat.
Admitted.

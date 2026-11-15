(* Statement-only formalization of PutnamBench corpus artifact putnam_2025_a3
   (putnambench__rocq__putnam_2025_a3): Alice has no winning strategy in the
   non-repeating ternary-string game for any positive string length. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Vectors.Fin.

Import ListNotations.

Definition putnam_2025_a3_GameString (n : nat) : Type :=
  Fin.t n -> Fin.t 3.

Definition putnam_2025_a3_fin_value
    {n : nat} (i : Fin.t n) : nat :=
  proj1_sig (Fin.to_nat i).

Definition putnam_2025_a3_initial_state
    (n : nat) : putnam_2025_a3_GameString n :=
  fun _ => @Fin.F1 2.

Definition putnam_2025_a3_same_game_string
    {n : nat}
    (left right : putnam_2025_a3_GameString n) : Prop :=
  forall i : Fin.t n, left i = right i.

Fixpoint putnam_2025_a3_member_by
    {A : Type}
    (equivalent : A -> A -> Prop)
    (item : A)
    (items : list A) : Prop :=
  match items with
  | [] => False
  | head :: tail =>
      equivalent item head \/
      putnam_2025_a3_member_by equivalent item tail
  end.

Fixpoint putnam_2025_a3_no_duplicates_by
    {A : Type}
    (equivalent : A -> A -> Prop)
    (items : list A) : Prop :=
  match items with
  | [] => True
  | head :: tail =>
      ~ putnam_2025_a3_member_by equivalent head tail /\
      putnam_2025_a3_no_duplicates_by equivalent tail
  end.

Definition putnam_2025_a3_is_valid_move
    {n : nat}
    (before after : putnam_2025_a3_GameString n) : Prop :=
  (exists! i : Fin.t n, before i <> after i) /\
  forall i : Fin.t n,
    before i <> after i ->
    S (putnam_2025_a3_fin_value (before i)) =
      putnam_2025_a3_fin_value (after i) \/
    S (putnam_2025_a3_fin_value (after i)) =
      putnam_2025_a3_fin_value (before i).

Fixpoint putnam_2025_a3_move_chain
    {A : Type}
    (relation : A -> A -> Prop)
    (start : A)
    (items : list A) : Prop :=
  match items with
  | [] => True
  | next :: tail =>
      relation start next /\
      putnam_2025_a3_move_chain relation next tail
  end.

Definition putnam_2025_a3_is_valid_game_play
    {n : nat}
    (play : list (putnam_2025_a3_GameString n)) : Prop :=
  putnam_2025_a3_move_chain
    putnam_2025_a3_is_valid_move
    (putnam_2025_a3_initial_state n)
    play /\
  putnam_2025_a3_no_duplicates_by
    putnam_2025_a3_same_game_string
    (putnam_2025_a3_initial_state n :: play).

Inductive putnam_2025_a3_HasWinningStrategy
    (n : nat) :
    list (putnam_2025_a3_GameString n) -> Prop :=
  | putnam_2025_a3_winning_move :
      forall
        (play : list (putnam_2025_a3_GameString n))
        (move : putnam_2025_a3_GameString n),
        putnam_2025_a3_is_valid_game_play (play ++ [move]) ->
        (forall reply : putnam_2025_a3_GameString n,
          putnam_2025_a3_is_valid_game_play
            (play ++ [move; reply]) ->
          putnam_2025_a3_HasWinningStrategy n
            (play ++ [move; reply])) ->
        putnam_2025_a3_HasWinningStrategy n play.

Definition putnam_2025_a3_AliceHasWinningStrategy
    (n : nat) : Prop :=
  putnam_2025_a3_HasWinningStrategy n [].

Definition putnam_2025_a3_solution (_ : nat) : Prop :=
  False.

Theorem putnam_2025_a3 :
  forall n : nat,
    (1 <= n)%nat ->
    (putnam_2025_a3_solution n <->
     putnam_2025_a3_AliceHasWinningStrategy n).
Admitted.

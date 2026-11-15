(* Statement-only formalization of PutnamBench corpus artifact putnam_2012_b3:
   every round-robin tournament on 2n teams admits an injective choice of one
   winning team from each of its 2n-1 days. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Vectors.Fin.

Open Scope nat_scope.

Definition putnam_2012_b3_matchups (n : nat) : Type :=
  Fin.t (2 * n - 1) -> Fin.t (2 * n) -> Fin.t (2 * n).

Definition putnam_2012_b3_wins (n : nat) : Type :=
  Fin.t (2 * n - 1) -> Fin.t (2 * n) -> bool.

Definition putnam_2012_b3_daily_games
    (n : nat) (matchups : putnam_2012_b3_matchups n) : Prop :=
  forall (d : Fin.t (2 * n - 1)) (t : Fin.t (2 * n)),
    matchups d t <> t /\
    matchups d (matchups d t) = t.

Definition putnam_2012_b3_all_matchups
    (n : nat) (matchups : putnam_2012_b3_matchups n) : Prop :=
  forall t1 t2 : Fin.t (2 * n),
    t1 <> t2 ->
    exists d : Fin.t (2 * n - 1), matchups d t1 = t2.

Definition putnam_2012_b3_valid_wins
    (n : nat)
    (matchups : putnam_2012_b3_matchups n)
    (wins : putnam_2012_b3_wins n) : Prop :=
  forall (d : Fin.t (2 * n - 1)) (t : Fin.t (2 * n)),
    wins d t = negb (wins d (matchups d t)).

Definition putnam_2012_b3_winning_choice
    (n : nat) (wins : putnam_2012_b3_wins n) : Prop :=
  exists choices : Fin.t (2 * n - 1) -> Fin.t (2 * n),
    (forall d : Fin.t (2 * n - 1), wins d (choices d) = true) /\
    (forall d1 d2 : Fin.t (2 * n - 1),
      choices d1 = choices d2 ->
      d1 = d2).

Definition putnam_2012_b3_solution : Prop := True.

Theorem putnam_2012_b3 :
  (forall n : nat,
    (1 <= n)%nat ->
    forall
      (matchups : putnam_2012_b3_matchups n)
      (wins : putnam_2012_b3_wins n),
      putnam_2012_b3_daily_games n matchups /\
      putnam_2012_b3_all_matchups n matchups /\
      putnam_2012_b3_valid_wins n matchups wins ->
      putnam_2012_b3_winning_choice n wins) <->
  putnam_2012_b3_solution.
Admitted.

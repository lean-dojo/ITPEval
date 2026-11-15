(* Statement-only formalization of PutnamBench corpus artifact putnam_2010_b3:
   characterization of the positive integers for which every distribution of
   2010n balls among 2010 indexed boxes can be made uniform by the prescribed
   box-to-box moves; this file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Vectors.Fin.

Open Scope nat_scope.

Definition putnam_2010_b3_configuration : Type :=
  Fin.t 2010 -> nat.

Fixpoint putnam_2010_b3_fin_sum
    (m : nat) : (Fin.t m -> nat) -> nat :=
  match m as k return (Fin.t k -> nat) -> nat with
  | O => fun _ => 0
  | S k =>
      fun f =>
        f Fin.F1 +
        putnam_2010_b3_fin_sum k (fun i => f (Fin.FS i))
  end.

Definition putnam_2010_b3_index
    {m : nat} (i : Fin.t m) : nat :=
  proj1_sig (Fin.to_nat i).

Definition putnam_2010_b3_move_amount
    (i : Fin.t 2010) : nat :=
  putnam_2010_b3_index i + 1.

Definition putnam_2010_b3_transitions
    (P : nat -> putnam_2010_b3_configuration)
    (T : nat) : Prop :=
  forall t : nat,
    t < T ->
    exists i j : Fin.t 2010,
      i <> j /\
      P t i >= putnam_2010_b3_move_amount i /\
      P (t + 1) i =
        P t i - putnam_2010_b3_move_amount i /\
      P (t + 1) j =
        P t j + putnam_2010_b3_move_amount i /\
      forall k : Fin.t 2010,
        k <> i ->
        k <> j ->
        P (t + 1) k = P t k.

Definition putnam_2010_b3_solution (n : nat) : Prop :=
  1005 <= n.

Theorem putnam_2010_b3
    (n : nat)
    (hn : 0 < n) :
  (forall B : putnam_2010_b3_configuration,
      putnam_2010_b3_fin_sum 2010 B = 2010 * n ->
      exists
        (P : nat -> putnam_2010_b3_configuration)
        (T : nat),
        P 0 = B /\
        putnam_2010_b3_transitions P T /\
        forall i : Fin.t 2010, P T i = n) <->
  putnam_2010_b3_solution n.
Admitted.

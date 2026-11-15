(* Statement-only formalization of PutnamBench artifact putnam_1987_a6:
   convergence of a series weighted by zero digits in base 3; this file
   contains no proof. *)

From Stdlib Require Import Reals List Arith.PeanoNat SeqSeries.

Open Scope R_scope.

Fixpoint putnam_1987_a6_digits_b3_fuel
    (fuel n : nat) : list nat :=
  match fuel with
  | O => nil
  | S fuel' =>
      if Nat.ltb n 3
      then cons n nil
      else cons (Nat.modulo n 3)
                (putnam_1987_a6_digits_b3_fuel fuel' (Nat.div n 3))
  end.

Definition putnam_1987_a6_digits_b3 (n : nat) : list nat :=
  putnam_1987_a6_digits_b3_fuel (S n) n.

Fixpoint putnam_1987_a6_count_zeros (digits : list nat) : nat :=
  match digits with
  | nil => O
  | cons d rest =>
      if Nat.eqb d 0
      then S (putnam_1987_a6_count_zeros rest)
      else putnam_1987_a6_count_zeros rest
  end.

Definition putnam_1987_a6_zero_count (n : nat) : nat :=
  putnam_1987_a6_count_zeros (putnam_1987_a6_digits_b3 n).

Definition putnam_1987_a6_solution (x : R) : Prop :=
  0 < x /\ x < 25.

Definition putnam_1987_a6_summable (u : nat -> R) : Prop :=
  exists limit : R, Un_cv (fun n : nat => sum_f_R0 u n) limit.

Theorem putnam_1987_a6 :
  forall x : R,
    (0 < x /\
     putnam_1987_a6_summable
       (fun k : nat =>
          x ^ putnam_1987_a6_zero_count (S k) /
          INR (S k) ^ 3)) <->
    putnam_1987_a6_solution x.
Admitted.

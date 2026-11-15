(* Statement-only formalization of PutnamBench corpus artifact putnam_2015_b3:
   characterization of real 2 by 2 arithmetic-progression matrices having
   a power of exponent greater than one with the same property. This file
   contains no proof. *)

From Stdlib Require Import Vectors.Fin Reals Arith.PeanoNat.

Open Scope R_scope.

Definition putnam_2015_b3_matrix : Type :=
  Fin.t 2 -> Fin.t 2 -> R.

Definition putnam_2015_b3_index0 : Fin.t 2 :=
  Fin.F1.

Definition putnam_2015_b3_index1 : Fin.t 2 :=
  Fin.FS Fin.F1.

Definition putnam_2015_b3_matrix_mul
    (A B : putnam_2015_b3_matrix) : putnam_2015_b3_matrix :=
  fun i j =>
    A i putnam_2015_b3_index0 *
      B putnam_2015_b3_index0 j +
    A i putnam_2015_b3_index1 *
      B putnam_2015_b3_index1 j.

Definition putnam_2015_b3_identity : putnam_2015_b3_matrix :=
  fun i j => if Fin.eq_dec i j then 1 else 0.

Fixpoint putnam_2015_b3_matrix_power
    (A : putnam_2015_b3_matrix)
    (k : nat) : putnam_2015_b3_matrix :=
  match k with
  | O => putnam_2015_b3_identity
  | S n =>
      putnam_2015_b3_matrix_mul
        (putnam_2015_b3_matrix_power A n) A
  end.

Definition putnam_2015_b3_arithmetic_progression
    (A : putnam_2015_b3_matrix) : Prop :=
  A putnam_2015_b3_index0 putnam_2015_b3_index1 -
      A putnam_2015_b3_index0 putnam_2015_b3_index0 =
    A putnam_2015_b3_index1 putnam_2015_b3_index0 -
      A putnam_2015_b3_index0 putnam_2015_b3_index1 /\
  A putnam_2015_b3_index1 putnam_2015_b3_index0 -
      A putnam_2015_b3_index0 putnam_2015_b3_index1 =
    A putnam_2015_b3_index1 putnam_2015_b3_index1 -
      A putnam_2015_b3_index1 putnam_2015_b3_index0.

Definition putnam_2015_b3_solution
    (A : putnam_2015_b3_matrix) : Prop :=
  (exists alpha : R,
      forall i j : Fin.t 2, A i j = alpha) \/
  (exists beta : R,
      A putnam_2015_b3_index0 putnam_2015_b3_index0 =
        beta * (-3) /\
      A putnam_2015_b3_index0 putnam_2015_b3_index1 =
        beta * (-1) /\
      A putnam_2015_b3_index1 putnam_2015_b3_index0 =
        beta * 1 /\
      A putnam_2015_b3_index1 putnam_2015_b3_index1 =
        beta * 3).

Theorem putnam_2015_b3
    (M : putnam_2015_b3_matrix)
    (S : putnam_2015_b3_matrix -> Prop)
    (hS : S = putnam_2015_b3_arithmetic_progression) :
  (S M /\
    exists k : nat,
      (1 < k)%nat /\
      S (putnam_2015_b3_matrix_power M k)) <->
  putnam_2015_b3_solution M.
Admitted.

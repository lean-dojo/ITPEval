(* Statement-only formalization of PutnamBench corpus artifact putnam_2025_a4:
   the least dimension of 2025 real square matrices whose commutation graph
   is the cycle on their indices. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Reals Vectors.Fin.

Open Scope R_scope.

Definition putnam_2025_a4_matrix (n : nat) : Type :=
  Fin.t n -> Fin.t n -> RbaseSymbolsImpl.R.

Fixpoint putnam_2025_a4_fin_sum
    (n : nat) :
    (Fin.t n -> RbaseSymbolsImpl.R) -> RbaseSymbolsImpl.R :=
  match n as m return
    (Fin.t m -> RbaseSymbolsImpl.R) -> RbaseSymbolsImpl.R with
  | O => fun _ => 0
  | S k =>
      fun f =>
        f Fin.F1 +
        putnam_2025_a4_fin_sum k (fun i => f (Fin.FS i))
  end.

Definition putnam_2025_a4_matrix_mul
    {n : nat}
    (A B : putnam_2025_a4_matrix n) :
    putnam_2025_a4_matrix n :=
  fun i j =>
    putnam_2025_a4_fin_sum n (fun k => A i k * B k j).

Definition putnam_2025_a4_matrix_eq
    {n : nat}
    (A B : putnam_2025_a4_matrix n) : Prop :=
  forall i j : Fin.t n, A i j = B i j.

Fixpoint putnam_2025_a4_fin_value
    {n : nat} (i : Fin.t n) : nat :=
  match i with
  | Fin.F1 => 0%nat
  | Fin.FS j => S (putnam_2025_a4_fin_value j)
  end.

Definition putnam_2025_a4_feasible_dimension (k : nat) : Prop :=
  exists A : Fin.t 2025 -> putnam_2025_a4_matrix k,
    forall i j : Fin.t 2025,
      (putnam_2025_a4_fin_value i <= putnam_2025_a4_fin_value j)%nat ->
      (putnam_2025_a4_matrix_eq
         (putnam_2025_a4_matrix_mul (A i) (A j))
         (putnam_2025_a4_matrix_mul (A j) (A i)) <->
       (putnam_2025_a4_fin_value j -
        putnam_2025_a4_fin_value i = 0)%nat \/
       (putnam_2025_a4_fin_value j -
        putnam_2025_a4_fin_value i = 1)%nat \/
       (putnam_2025_a4_fin_value j -
        putnam_2025_a4_fin_value i = 2024)%nat).

Definition putnam_2025_a4_is_least
    (property : nat -> Prop) (least : nat) : Prop :=
  property least /\
  forall candidate : nat,
    property candidate ->
    (least <= candidate)%nat.

Definition putnam_2025_a4_solution : nat := 3%nat.

Theorem putnam_2025_a4 :
  putnam_2025_a4_is_least
    putnam_2025_a4_feasible_dimension
    putnam_2025_a4_solution.
Admitted.

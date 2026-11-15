(* Statement-only formalization of PutnamBench corpus artifact putnam_2024_a6
   (putnambench__rocq__putnam_2024_a6): the Hankel determinant formed from
   coefficients of a specified algebraic real power series. This file
   contains no proof. *)

From Stdlib Require Import Lists.List Arith.PeanoNat Vectors.Fin Reals.

Import ListNotations.
Open Scope R_scope.

Fixpoint putnam_2024_a6_partial_sum
    (u : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S k => putnam_2024_a6_partial_sum u k + u k
  end.

Definition putnam_2024_a6_series_sum
    (u : nat -> R) (value : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall m : nat,
        (N <= m)%nat ->
        Rabs (putnam_2024_a6_partial_sum u m - value) < epsilon.

Definition putnam_2024_a6_generating_function
    (c : nat -> R) : Prop :=
  exists radius : R,
    0 < radius /\
    forall x : R,
      Rabs x < radius ->
      putnam_2024_a6_series_sum
        (fun k : nat => c k * x ^ k)
        ((1 - 3 * x - sqrt (1 - 14 * x + 9 * x ^ 2)) / 4).

Fixpoint putnam_2024_a6_fin_list
    (n : nat) : list (Fin.t n) :=
  match n as m return list (Fin.t m) with
  | O => []
  | S k =>
      Fin.F1 :: map Fin.FS (putnam_2024_a6_fin_list k)
  end.

Fixpoint putnam_2024_a6_sum (xs : list R) : R :=
  match xs with
  | [] => 0
  | x :: rest => x + putnam_2024_a6_sum rest
  end.

Definition putnam_2024_a6_delete_nth
    {T : Type} (j : nat) (xs : list T) : list T :=
  firstn j xs ++ skipn (S j) xs.

Definition putnam_2024_a6_cofactor_sign (j : nat) : R :=
  if Nat.even j then 1 else -1.

Fixpoint putnam_2024_a6_list_det
    (n : nat) (M : list (list R)) {struct n} : R :=
  match n with
  | O => 1
  | S k =>
      match M with
      | [] => 0
      | row :: rows =>
          putnam_2024_a6_sum
            (map
              (fun j : nat =>
                putnam_2024_a6_cofactor_sign j *
                nth j row 0 *
                putnam_2024_a6_list_det k
                  (map (putnam_2024_a6_delete_nth j) rows))
              (seq 0 (S k)))
      end
  end.

Definition putnam_2024_a6_matrix (n : nat) : Type :=
  Fin.t n -> Fin.t n -> R.

Definition putnam_2024_a6_rows
    (n : nat) (A : putnam_2024_a6_matrix n) :
    list (list R) :=
  map
    (fun i =>
      map (fun j => A i j) (putnam_2024_a6_fin_list n))
    (putnam_2024_a6_fin_list n).

Definition putnam_2024_a6_determinant
    (n : nat) (A : putnam_2024_a6_matrix n) : R :=
  putnam_2024_a6_list_det n (putnam_2024_a6_rows n A).

Definition putnam_2024_a6_index
    {n : nat} (i : Fin.t n) : nat :=
  proj1_sig (Fin.to_nat i).

Definition putnam_2024_a6_hankel_matrix
    (c : nat -> R) (n : nat) : putnam_2024_a6_matrix n :=
  fun i j =>
    c ((putnam_2024_a6_index i +
        putnam_2024_a6_index j + 1)%nat).

Definition putnam_2024_a6_solution (n : nat) : R :=
  10 ^ ((n * (n - 1) / 2)%nat).

Theorem putnam_2024_a6 :
  forall (c : nat -> R) (n : nat),
    putnam_2024_a6_generating_function c ->
    (0 < n)%nat ->
    putnam_2024_a6_determinant n
      (putnam_2024_a6_hankel_matrix c n) =
    putnam_2024_a6_solution n.
Admitted.

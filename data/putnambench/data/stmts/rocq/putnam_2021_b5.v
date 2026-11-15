(* Statement-only formalization of PutnamBench corpus artifact putnam_2021_b5:
   integer matrices whose nonempty principal minors all have odd determinant
   retain that property under every positive matrix power. This file contains
   no proof. *)

From Stdlib Require Import ZArith Lists.List Vectors.Fin Arith.PeanoNat.

Import ListNotations.
Open Scope Z_scope.

Definition putnam_2021_b5_matrix (n : nat) : Type :=
  Fin.t n -> Fin.t n -> Z.

Fixpoint putnam_2021_b5_indices (n : nat) : list (Fin.t n) :=
  match n with
  | O => []
  | S k => Fin.F1 :: map Fin.FS (putnam_2021_b5_indices k)
  end.

Fixpoint putnam_2021_b5_zsum (xs : list Z) : Z :=
  match xs with
  | [] => 0
  | x :: rest => x + putnam_2021_b5_zsum rest
  end.

Definition putnam_2021_b5_matrix_mul
    {n : nat}
    (A B : putnam_2021_b5_matrix n) :
    putnam_2021_b5_matrix n :=
  fun i j =>
    putnam_2021_b5_zsum
      (map
        (fun r => A i r * B r j)
        (putnam_2021_b5_indices n)).

Definition putnam_2021_b5_identity
    (n : nat) : putnam_2021_b5_matrix n :=
  fun i j =>
    if Fin.eq_dec i j then 1 else 0.

Fixpoint putnam_2021_b5_matrix_power
    {n : nat}
    (A : putnam_2021_b5_matrix n)
    (k : nat) : putnam_2021_b5_matrix n :=
  match k with
  | O => putnam_2021_b5_identity n
  | S l =>
      putnam_2021_b5_matrix_mul
        (putnam_2021_b5_matrix_power A l) A
  end.

Definition putnam_2021_b5_delete_nth
    {T : Type} (j : nat) (xs : list T) : list T :=
  firstn j xs ++ skipn (S j) xs.

Definition putnam_2021_b5_cofactor_sign (j : nat) : Z :=
  if Nat.even j then 1 else -1.

Fixpoint putnam_2021_b5_det
    (n : nat) (M : list (list Z)) {struct n} : Z :=
  match n with
  | O => 1
  | S k =>
      match M with
      | [] => 0
      | row :: rows =>
          putnam_2021_b5_zsum
            (map
              (fun j : nat =>
                putnam_2021_b5_cofactor_sign j *
                nth j row 0 *
                putnam_2021_b5_det k
                  (map (putnam_2021_b5_delete_nth j) rows))
              (seq 0 (S k)))
      end
  end.

Definition putnam_2021_b5_principal_minor
    {n : nat}
    (A : putnam_2021_b5_matrix n)
    {m : nat}
    (reindex : Fin.t m -> Fin.t n) : list (list Z) :=
  map
    (fun i =>
      map
        (fun j => A (reindex i) (reindex j))
        (putnam_2021_b5_indices m))
    (putnam_2021_b5_indices m).

Definition putnam_2021_b5_very_odd
    {n : nat}
    (A : putnam_2021_b5_matrix n) : Prop :=
  forall m : nat,
    (1 <= m <= n)%nat ->
    forall reindex : Fin.t m -> Fin.t n,
      (forall x y : Fin.t m,
        reindex x = reindex y -> x = y) ->
      Z.odd
        (putnam_2021_b5_det m
          (putnam_2021_b5_principal_minor A reindex)) =
        true.

Theorem putnam_2021_b5
    (n : nat)
    (npos : (1 <= n)%nat) :
  forall A : putnam_2021_b5_matrix n,
    putnam_2021_b5_very_odd A ->
    forall k : nat,
      (1 <= k)%nat ->
      putnam_2021_b5_very_odd
        (putnam_2021_b5_matrix_power A k).
Admitted.

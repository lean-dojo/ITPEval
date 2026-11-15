(* Statement-only formalization of PutnamBench corpus artifact putnam_2023_b6:
   the determinant of the integer matrix counting nonnegative solutions to
   a*i + b*j = n for 1 <= i,j <= n. This file contains no proof. *)

From Stdlib Require Import Lists.List Vectors.Fin ZArith Arith.PeanoNat.

Import ListNotations.

Definition putnam_2023_b6_matrix (n : nat) : Type :=
  Fin.t n -> Fin.t n -> Z.

Definition putnam_2023_b6_fin_index
    {n : nat} (i : Fin.t n) : nat :=
  proj1_sig (Fin.to_nat i).

Fixpoint putnam_2023_b6_fin_list
    (n : nat) : list (Fin.t n) :=
  match n as k return list (Fin.t k) with
  | O => []
  | S k =>
      Fin.F1 :: map Fin.FS (putnam_2023_b6_fin_list k)
  end.

Fixpoint putnam_2023_b6_zsum_upto
    (bound : nat) (f : nat -> Z) : Z :=
  match bound with
  | O => f O
  | S k => (putnam_2023_b6_zsum_upto k f + f (S k))%Z
  end.

Definition putnam_2023_b6_solution_count
    {n : nat} (i j : Fin.t n) : Z :=
  putnam_2023_b6_zsum_upto n
    (fun a =>
      putnam_2023_b6_zsum_upto n
        (fun b =>
          if Nat.eqb
               (a * (putnam_2023_b6_fin_index i + 1) +
                b * (putnam_2023_b6_fin_index j + 1))
               n
          then 1%Z
          else 0%Z)).

Definition putnam_2023_b6_rows
    {n : nat} (A : putnam_2023_b6_matrix n) :
    list (list Z) :=
  map
    (fun i =>
      map (fun j => A i j) (putnam_2023_b6_fin_list n))
    (putnam_2023_b6_fin_list n).

Definition putnam_2023_b6_delete_nth
    {T : Type} (j : nat) (xs : list T) : list T :=
  firstn j xs ++ skipn (S j) xs.

Definition putnam_2023_b6_cofactor_sign (j : nat) : Z :=
  if Nat.even j then 1%Z else (-1)%Z.

Fixpoint putnam_2023_b6_zsum (xs : list Z) : Z :=
  match xs with
  | [] => 0%Z
  | x :: rest => (x + putnam_2023_b6_zsum rest)%Z
  end.

Fixpoint putnam_2023_b6_list_det
    (n : nat) (M : list (list Z)) {struct n} : Z :=
  match n with
  | O => 1%Z
  | S k =>
      match M with
      | [] => 0%Z
      | row :: rows =>
          putnam_2023_b6_zsum
            (map
              (fun j : nat =>
                (putnam_2023_b6_cofactor_sign j *
                 nth j row 0%Z *
                 putnam_2023_b6_list_det k
                   (map (putnam_2023_b6_delete_nth j) rows))%Z)
              (seq 0 (S k)))
      end
  end.

Definition putnam_2023_b6_determinant
    {n : nat} (A : putnam_2023_b6_matrix n) : Z :=
  putnam_2023_b6_list_det n (putnam_2023_b6_rows A).

Definition putnam_2023_b6_solution (n : nat) : Z :=
  let half := Nat.div (S n) 2 in
  (Z.pow (-1) (Z.of_nat (S half)) * 2 * Z.of_nat half)%Z.

Theorem putnam_2023_b6
    (n : nat)
    (S : putnam_2023_b6_matrix n)
    (npos : (0 < n)%nat)
    (hS :
      forall i j : Fin.t n,
        S i j = putnam_2023_b6_solution_count i j) :
  putnam_2023_b6_determinant S =
  putnam_2023_b6_solution n.
Admitted.

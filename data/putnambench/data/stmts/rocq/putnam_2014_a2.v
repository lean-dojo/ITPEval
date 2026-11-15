(* Statement-only formalization of PutnamBench corpus artifact putnam_2014_a2:
   the determinant of the positive-dimensional real matrix with entries
   reciprocal to the minimum of their one-based indices. This file contains
   no proof. *)

From Stdlib Require Import Lists.List Arith.PeanoNat Arith.Factorial
  Vectors.Fin Reals.

Import ListNotations.
Open Scope R_scope.

Fixpoint putnam_2014_a2_fin_list
    (n : nat) : list (Fin.t n) :=
  match n as m return list (Fin.t m) with
  | O => []
  | S k =>
      Fin.F1 :: map Fin.FS (putnam_2014_a2_fin_list k)
  end.

Fixpoint putnam_2014_a2_sum (xs : list R) : R :=
  match xs with
  | [] => 0
  | x :: rest => x + putnam_2014_a2_sum rest
  end.

Definition putnam_2014_a2_delete_nth
    {T : Type} (j : nat) (xs : list T) : list T :=
  firstn j xs ++ skipn (S j) xs.

Definition putnam_2014_a2_cofactor_sign (j : nat) : R :=
  if Nat.even j then 1 else -1.

Fixpoint putnam_2014_a2_list_det
    (n : nat) (M : list (list R)) {struct n} : R :=
  match n with
  | O => 1
  | S k =>
      match M with
      | [] => 0
      | row :: rows =>
          putnam_2014_a2_sum
            (map
              (fun j : nat =>
                putnam_2014_a2_cofactor_sign j *
                nth j row 0 *
                putnam_2014_a2_list_det k
                  (map (putnam_2014_a2_delete_nth j) rows))
              (seq 0 (S k)))
      end
  end.

Definition putnam_2014_a2_matrix (n : nat) : Type :=
  Fin.t n -> Fin.t n -> R.

Definition putnam_2014_a2_rows
    (n : nat) (A : putnam_2014_a2_matrix n) :
    list (list R) :=
  map
    (fun i =>
      map (fun j => A i j) (putnam_2014_a2_fin_list n))
    (putnam_2014_a2_fin_list n).

Definition putnam_2014_a2_determinant
    (n : nat) (A : putnam_2014_a2_matrix n) : R :=
  putnam_2014_a2_list_det n (putnam_2014_a2_rows n A).

Definition putnam_2014_a2_index
    {n : nat} (i : Fin.t n) : nat :=
  proj1_sig (Fin.to_nat i).

Definition putnam_2014_a2_solution (n : nat) : R :=
  (-1) ^ (n - 1) /
  (INR (fact (n - 1)) * INR (fact n)).

Theorem putnam_2014_a2
    (n : nat)
    (A : putnam_2014_a2_matrix n)
    (npos : (0 < n)%nat)
    (hA :
      forall i j : Fin.t n,
        A i j =
        1 / INR
          (Nat.min
            (S (putnam_2014_a2_index i))
            (S (putnam_2014_a2_index j)))) :
  putnam_2014_a2_determinant n A =
  putnam_2014_a2_solution n.
Admitted.

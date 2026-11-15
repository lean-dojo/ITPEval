(* Statement-only formalization of PutnamBench corpus artifact putnam_2018_a2:
   the determinant of the intersection-incidence matrix indexed by all
   nonempty subsets of a finite interval. This file contains no proof. *)

From Stdlib Require Import Lists.List Arith.PeanoNat Vectors.Fin Reals
  Ensembles ClassicalDescription.

Import ListNotations.
Open Scope R_scope.

Definition putnam_2018_a2_dimension (n : nat) : nat :=
  (Nat.pow 2 n - 1)%nat.

Definition putnam_2018_a2_matrix (n : nat) : Type :=
  Fin.t (putnam_2018_a2_dimension n) ->
  Fin.t (putnam_2018_a2_dimension n) ->
  R.

Definition putnam_2018_a2_interval (n : nat) : Ensemble nat :=
  fun x : nat => (1 <= x <= n)%nat.

Definition putnam_2018_a2_nonempty_subset
    (n : nat) (A : Ensemble nat) : Prop :=
  (exists x : nat, In nat A x) /\
  Included nat A (putnam_2018_a2_interval n).

Definition putnam_2018_a2_intersects
    (A B : Ensemble nat) : Prop :=
  exists x : nat, In nat A x /\ In nat B x.

Definition putnam_2018_a2_entry
    (A B : Ensemble nat) : R :=
  if excluded_middle_informative (putnam_2018_a2_intersects A B)
  then 1
  else 0.

Fixpoint putnam_2018_a2_fin_list
    (n : nat) : list (Fin.t n) :=
  match n as k return list (Fin.t k) with
  | O => []
  | S k =>
      Fin.F1 :: map Fin.FS (putnam_2018_a2_fin_list k)
  end.

Definition putnam_2018_a2_rows
    {T : Type} (n : nat) (A : Fin.t n -> Fin.t n -> T) :
    list (list T) :=
  map
    (fun i =>
      map (fun j => A i j) (putnam_2018_a2_fin_list n))
    (putnam_2018_a2_fin_list n).

Fixpoint putnam_2018_a2_sum (xs : list R) : R :=
  match xs with
  | [] => 0
  | x :: rest => x + putnam_2018_a2_sum rest
  end.

Definition putnam_2018_a2_delete_nth
    {T : Type} (j : nat) (xs : list T) : list T :=
  firstn j xs ++ skipn (S j) xs.

Definition putnam_2018_a2_cofactor_sign (j : nat) : R :=
  if Nat.even j then 1 else -1.

Fixpoint putnam_2018_a2_list_det
    (n : nat) (M : list (list R)) {struct n} : R :=
  match n with
  | O => 1
  | S k =>
      match M with
      | [] => 0
      | row :: rows =>
          putnam_2018_a2_sum
            (map
              (fun j : nat =>
                putnam_2018_a2_cofactor_sign j *
                nth j row 0 *
                putnam_2018_a2_list_det k
                  (map (putnam_2018_a2_delete_nth j) rows))
              (seq 0 (S k)))
      end
  end.

Definition putnam_2018_a2_determinant
    (n : nat) (A : Fin.t n -> Fin.t n -> R) : R :=
  putnam_2018_a2_list_det n (putnam_2018_a2_rows n A).

Definition putnam_2018_a2_solution (n : nat) : R :=
  if Nat.eqb n 1 then 1 else -1.

Theorem putnam_2018_a2
    (n : nat)
    (S :
      Fin.t (putnam_2018_a2_dimension n) ->
      Ensemble nat)
    (M : putnam_2018_a2_matrix n)
    (npos : (1 <= n)%nat)
    (hS :
      forall A : Ensemble nat,
        (exists i : Fin.t (putnam_2018_a2_dimension n),
            Same_set nat (S i) A) <->
        putnam_2018_a2_nonempty_subset n A)
    (hM :
      forall i j : Fin.t (putnam_2018_a2_dimension n),
        M i j = putnam_2018_a2_entry (S i) (S j)) :
  putnam_2018_a2_determinant
    (putnam_2018_a2_dimension n) M =
  putnam_2018_a2_solution n.
Admitted.

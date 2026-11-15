(* Statement-only formalization of PutnamBench corpus artifact putnam_2019_b3:
   an orthogonal real matrix with no eigenvalue 1 gains eigenvalue 1 after
   multiplication by a Householder reflection. This file contains no proof. *)

From Stdlib Require Import Lists.List Vectors.Fin Reals Arith.PeanoNat.

Import ListNotations.
Open Scope R_scope.

Definition putnam_2019_b3_matrix (n : nat) : Type :=
  Fin.t n -> Fin.t n -> R.

Definition putnam_2019_b3_matrix_eq {n : nat}
    (A B : putnam_2019_b3_matrix n) : Prop :=
  forall i j : Fin.t n, A i j = B i j.

Fixpoint putnam_2019_b3_fin_sum
    (n : nat) : (Fin.t n -> R) -> R :=
  match n as k return (Fin.t k -> R) -> R with
  | O => fun _ => 0
  | S k =>
      fun f =>
        f Fin.F1 +
        putnam_2019_b3_fin_sum k (fun i => f (Fin.FS i))
  end.

Definition putnam_2019_b3_identity
    (n : nat) : putnam_2019_b3_matrix n :=
  fun i j => if Fin.eq_dec i j then 1 else 0.

Definition putnam_2019_b3_matrix_mul {n : nat}
    (A B : putnam_2019_b3_matrix n) :
    putnam_2019_b3_matrix n :=
  fun i j =>
    putnam_2019_b3_fin_sum n (fun k => A i k * B k j).

Definition putnam_2019_b3_matrix_sub {n : nat}
    (A B : putnam_2019_b3_matrix n) :
    putnam_2019_b3_matrix n :=
  fun i j => A i j - B i j.

Definition putnam_2019_b3_row_dot {n : nat}
    (A : putnam_2019_b3_matrix n)
    (i j : Fin.t n) : R :=
  putnam_2019_b3_fin_sum n (fun k => A i k * A j k).

Definition putnam_2019_b3_column_dot {n : nat}
    (A : putnam_2019_b3_matrix n)
    (i j : Fin.t n) : R :=
  putnam_2019_b3_fin_sum n (fun k => A k i * A k j).

Definition putnam_2019_b3_reflection
    {n : nat} (u : Fin.t n -> R) :
    putnam_2019_b3_matrix n :=
  fun i j =>
    putnam_2019_b3_identity n i j - 2 * (u i * u j).

Fixpoint putnam_2019_b3_fin_list
    (n : nat) : list (Fin.t n) :=
  match n as k return list (Fin.t k) with
  | O => []
  | S k =>
      Fin.F1 :: map Fin.FS (putnam_2019_b3_fin_list k)
  end.

Definition putnam_2019_b3_rows
    {n : nat} (A : putnam_2019_b3_matrix n) :
    list (list R) :=
  map
    (fun i =>
      map (fun j => A i j) (putnam_2019_b3_fin_list n))
    (putnam_2019_b3_fin_list n).

Definition putnam_2019_b3_delete_nth
    {T : Type} (j : nat) (xs : list T) : list T :=
  firstn j xs ++ skipn (S j) xs.

Definition putnam_2019_b3_cofactor_sign (j : nat) : R :=
  if Nat.even j then 1 else -1.

Fixpoint putnam_2019_b3_real_sum (xs : list R) : R :=
  match xs with
  | [] => 0
  | x :: rest => x + putnam_2019_b3_real_sum rest
  end.

Fixpoint putnam_2019_b3_list_det
    (n : nat) (M : list (list R)) {struct n} : R :=
  match n with
  | O => 1
  | S k =>
      match M with
      | [] => 0
      | row :: rows =>
          putnam_2019_b3_real_sum
            (map
              (fun j : nat =>
                putnam_2019_b3_cofactor_sign j *
                nth j row 0 *
                putnam_2019_b3_list_det k
                  (map (putnam_2019_b3_delete_nth j) rows))
              (seq 0 (S k)))
      end
  end.

Definition putnam_2019_b3_determinant
    {n : nat} (A : putnam_2019_b3_matrix n) : R :=
  putnam_2019_b3_list_det n (putnam_2019_b3_rows A).

Theorem putnam_2019_b3
    (n : nat)
    (hn : (0 < n)%nat)
    (Q : putnam_2019_b3_matrix n)
    (hQ0 :
      forall i j : Fin.t n,
        i <> j ->
        putnam_2019_b3_row_dot Q i j = 0 /\
        putnam_2019_b3_column_dot Q i j = 0)
    (hQ1 :
      forall i : Fin.t n,
        putnam_2019_b3_row_dot Q i i = 1 /\
        putnam_2019_b3_column_dot Q i i = 1)
    (u : Fin.t n -> R)
    (hu :
      putnam_2019_b3_fin_sum n (fun i => u i * u i) = 1)
    (P : putnam_2019_b3_matrix n)
    (hP :
      putnam_2019_b3_matrix_eq
        P (putnam_2019_b3_reflection u)) :
  putnam_2019_b3_determinant
      (putnam_2019_b3_matrix_sub
        Q (putnam_2019_b3_identity n)) <> 0 ->
  putnam_2019_b3_determinant
      (putnam_2019_b3_matrix_sub
        (putnam_2019_b3_matrix_mul P Q)
        (putnam_2019_b3_identity n)) = 0.
Admitted.

(* Statement-only formalization of PutnamBench corpus artifact putnam_2016_b4:
   the expected determinant of A - transpose A for a uniformly random
   2n-by-2n zero-one matrix. This file contains no proof. *)

From Stdlib Require Import Lists.List Arith.PeanoNat Arith.Factorial
  Vectors.Fin Reals.

Import ListNotations.
Open Scope R_scope.

Definition putnam_2016_b4_matrix (n : nat) : Type :=
  Fin.t n -> Fin.t n -> R.

Definition putnam_2016_b4_fin_index {n : nat} (i : Fin.t n) : nat :=
  proj1_sig (Fin.to_nat i).

Fixpoint putnam_2016_b4_fin_list
    (n : nat) : list (Fin.t n) :=
  match n as k return list (Fin.t k) with
  | O => []
  | S k =>
      Fin.F1 :: map Fin.FS (putnam_2016_b4_fin_list k)
  end.

Fixpoint putnam_2016_b4_bit_words (k : nat) : list (list bool) :=
  match k with
  | O => [[]]
  | S k' =>
      map (cons false) (putnam_2016_b4_bit_words k') ++
      map (cons true) (putnam_2016_b4_bit_words k')
  end.

Definition putnam_2016_b4_matrix_of_bits
    (n : nat) (bits : list bool) : putnam_2016_b4_matrix n :=
  fun i j =>
    if nth
         (putnam_2016_b4_fin_index i * n +
          putnam_2016_b4_fin_index j)%nat
         bits false
    then 1
    else 0.

Definition putnam_2016_b4_transpose
    {n : nat} (A : putnam_2016_b4_matrix n) :
    putnam_2016_b4_matrix n :=
  fun i j => A j i.

Definition putnam_2016_b4_matrix_sub
    {n : nat}
    (A B : putnam_2016_b4_matrix n) :
    putnam_2016_b4_matrix n :=
  fun i j => A i j - B i j.

Definition putnam_2016_b4_rows
    {T : Type} (n : nat) (A : Fin.t n -> Fin.t n -> T) :
    list (list T) :=
  map
    (fun i =>
      map (fun j => A i j) (putnam_2016_b4_fin_list n))
    (putnam_2016_b4_fin_list n).

Definition putnam_2016_b4_delete_nth
    {T : Type} (j : nat) (xs : list T) : list T :=
  firstn j xs ++ skipn (S j) xs.

Definition putnam_2016_b4_cofactor_sign (j : nat) : R :=
  if Nat.even j then 1 else -1.

Fixpoint putnam_2016_b4_real_sum (xs : list R) : R :=
  match xs with
  | [] => 0
  | x :: rest => x + putnam_2016_b4_real_sum rest
  end.

Fixpoint putnam_2016_b4_list_det
    (n : nat) (M : list (list R)) {struct n} : R :=
  match n with
  | O => 1
  | S k =>
      match M with
      | [] => 0
      | row :: rows =>
          putnam_2016_b4_real_sum
            (map
              (fun j : nat =>
                putnam_2016_b4_cofactor_sign j *
                nth j row 0 *
                putnam_2016_b4_list_det k
                  (map (putnam_2016_b4_delete_nth j) rows))
              (seq 0 (S k)))
      end
  end.

Definition putnam_2016_b4_determinant
    (n : nat) (A : putnam_2016_b4_matrix n) : R :=
  putnam_2016_b4_list_det n (putnam_2016_b4_rows n A).

Definition putnam_2016_b4_determinant_value
    (n : nat) (bits : list bool) : R :=
  let A := putnam_2016_b4_matrix_of_bits (2 * n) bits in
  putnam_2016_b4_determinant (2 * n)
    (putnam_2016_b4_matrix_sub A (putnam_2016_b4_transpose A)).

Definition putnam_2016_b4_all_matrices
    (n : nat) : list (list bool) :=
  putnam_2016_b4_bit_words ((2 * n) * (2 * n)).

Definition putnam_2016_b4_expected_value (n : nat) : R :=
  let matrices := putnam_2016_b4_all_matrices n in
  putnam_2016_b4_real_sum
    (map (putnam_2016_b4_determinant_value n) matrices) /
  INR (length matrices).

Definition putnam_2016_b4_solution (n : nat) : R :=
  INR (fact (2 * n)) /
  (INR (Nat.pow 4 n) * INR (fact n)).

Theorem putnam_2016_b4
    (n : nat)
    (npos : (1 <= n)%nat) :
  putnam_2016_b4_expected_value n =
  putnam_2016_b4_solution n.
Admitted.

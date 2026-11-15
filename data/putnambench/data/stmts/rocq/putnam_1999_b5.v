(* Statement-only formalization of PutnamBench corpus artifact putnam_1999_b5:
   the determinant of the identity plus an n-by-n cosine matrix indexed from
   1 through n. This file contains no proof. *)

From Stdlib Require Import Reals List Arith.PeanoNat.

Open Scope R_scope.

Fixpoint putnam_1999_b5_insert_everywhere
    (x : nat) (xs : list nat) : list (list nat) :=
  match xs with
  | nil => (x :: nil) :: nil
  | y :: ys =>
      (x :: y :: ys) ::
      map (cons y) (putnam_1999_b5_insert_everywhere x ys)
  end.

Fixpoint putnam_1999_b5_permutations
    (xs : list nat) : list (list nat) :=
  match xs with
  | nil => nil :: nil
  | x :: ys =>
      flat_map (putnam_1999_b5_insert_everywhere x)
        (putnam_1999_b5_permutations ys)
  end.

Fixpoint putnam_1999_b5_inversions_from
    (x : nat) (xs : list nat) : nat :=
  match xs with
  | nil => O
  | y :: ys =>
      (if Nat.ltb y x then 1%nat else O) +
      putnam_1999_b5_inversions_from x ys
  end.

Fixpoint putnam_1999_b5_inversions
    (xs : list nat) : nat :=
  match xs with
  | nil => O
  | x :: ys =>
      putnam_1999_b5_inversions_from x ys +
      putnam_1999_b5_inversions ys
  end.

Definition putnam_1999_b5_permutation_sign
    (p : list nat) : R :=
  if Nat.even (putnam_1999_b5_inversions p) then 1 else -1.

Fixpoint putnam_1999_b5_permutation_product
    (M : nat -> nat -> R) (rows columns : list nat) : R :=
  match rows, columns with
  | i :: is, j :: js =>
      M i j * putnam_1999_b5_permutation_product M is js
  | _, _ => 1
  end.

Fixpoint putnam_1999_b5_real_sum (xs : list R) : R :=
  match xs with
  | nil => 0
  | x :: ys => x + putnam_1999_b5_real_sum ys
  end.

Definition putnam_1999_b5_determinant
    (n : nat) (M : nat -> nat -> R) : R :=
  putnam_1999_b5_real_sum
    (map
      (fun p =>
        putnam_1999_b5_permutation_sign p *
        putnam_1999_b5_permutation_product M (seq O n) p)
      (putnam_1999_b5_permutations (seq O n))).

Definition putnam_1999_b5_solution (n : nat) : R :=
  1 - (INR n) ^ 2 / 4.

Theorem putnam_1999_b5
    (n : nat)
    (hn : (3 <= n)%nat)
    (theta : R)
    (htheta : theta = 2 * PI / INR n)
    (A : nat -> nat -> R)
    (hA : forall i j : nat,
      (i < n)%nat ->
      (j < n)%nat ->
      A i j =
        cos (INR (S i) * theta + INR (S j) * theta)) :
  putnam_1999_b5_determinant n
    (fun i j : nat =>
      (if Nat.eq_dec i j then 1 else 0) + A i j) =
  putnam_1999_b5_solution n.
Admitted.

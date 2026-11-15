(* Statement-only formalization of PutnamBench artifact putnam_1978_a2:
   the determinant formula for a real matrix with constant entries above and
   below the diagonal. This file contains no proof. *)

From Stdlib Require Import Reals List Arith.

Import ListNotations.
Open Scope R_scope.

Fixpoint putnam_1978_a2_sum (xs : list R) : R :=
  match xs with
  | [] => 0
  | x :: rest => x + putnam_1978_a2_sum rest
  end.

Definition putnam_1978_a2_delete_nth
    {T : Type} (j : nat) (xs : list T) : list T :=
  firstn j xs ++ skipn (S j) xs.

Definition putnam_1978_a2_cofactor_sign (j : nat) : R :=
  if Nat.even j then 1 else -1.

Fixpoint putnam_1978_a2_det
    (n : nat) (M : list (list R)) {struct n} : R :=
  match n with
  | O => 1
  | S k =>
      match M with
      | [] => 0
      | row :: rows =>
          putnam_1978_a2_sum
            (map
              (fun j : nat =>
                putnam_1978_a2_cofactor_sign j *
                nth j row 0 *
                putnam_1978_a2_det k
                  (map (putnam_1978_a2_delete_nth j) rows))
              (seq 0 (S k)))
      end
  end.

Definition putnam_1978_a2_matrix
    (n : nat) (a b : R) (c : list R) : list (list R) :=
  map
    (fun i : nat =>
      map
        (fun j : nat =>
          if Nat.ltb i j then a
          else if Nat.ltb j i then b
          else nth i c 0)
        (seq 0 n))
    (seq 0 n).

Definition putnam_1978_a2_polynomial (c : list R) (x : R) : R :=
  fold_right Rmult 1 (map (fun ci : R => ci - x) c).

Theorem putnam_1978_a2
    (n : nat)
    (npos : (0 < n)%nat)
    (a b : R)
    (hab : a <> b)
    (c : list R)
    (hc : length c = n)
    (A : list (list R))
    (hA : A = putnam_1978_a2_matrix n a b c)
    (p : R -> R)
    (hp : p = putnam_1978_a2_polynomial c) :
  putnam_1978_a2_det n A =
    (b * p a - a * p b) / (b - a).
Admitted.

(* Statement-only formalization of PutnamBench corpus artifact putnam_1992_b5:
   boundedness of the factorial-normalized determinants of the prescribed
   rational matrices; this file contains no proof. *)

From Stdlib Require Import QArith Qabs Lists.List Arith.PeanoNat Arith.Factorial.

Import ListNotations.
Open Scope Q_scope.

Fixpoint putnam_1992_b5_sum (xs : list Q) : Q :=
  match xs with
  | [] => 0
  | x :: rest => x + putnam_1992_b5_sum rest
  end.

Definition putnam_1992_b5_delete_nth
    {A : Type} (j : nat) (xs : list A) : list A :=
  firstn j xs ++ skipn (S j) xs.

Definition putnam_1992_b5_cofactor_sign (j : nat) : Q :=
  if Nat.even j then 1 else -1.

Fixpoint putnam_1992_b5_det
    (n : nat) (M : list (list Q)) {struct n} : Q :=
  match n with
  | O => 1
  | S k =>
      match M with
      | [] => 0
      | row :: rows =>
          putnam_1992_b5_sum
            (map
              (fun j : nat =>
                putnam_1992_b5_cofactor_sign j *
                nth j row 0 *
                putnam_1992_b5_det k
                  (map (putnam_1992_b5_delete_nth j) rows))
              (seq 0 (S k)))
      end
  end.

Definition putnam_1992_b5_matrix (n : nat) : list (list Q) :=
  map
    (fun i : nat =>
      map
        (fun j : nat =>
          if Nat.eqb i j
          then inject_Z (Z.of_nat ((i + 3)%nat))
          else 1)
        (seq 0 n))
    (seq 0 n).

Definition putnam_1992_b5_D (n : nat) : Q :=
  putnam_1992_b5_det
    (n - 1)%nat
    (putnam_1992_b5_matrix (n - 1)%nat).

Definition putnam_1992_b5_bounded : Prop :=
  exists r : Q,
    forall x : Q,
      (exists n : nat,
        (2 <= n)%nat /\
        putnam_1992_b5_D n /
          inject_Z (Z.of_nat (fact n)) = x) ->
      Qabs x <= r.

Definition putnam_1992_b5_solution : Prop := False.

Theorem putnam_1992_b5 :
  putnam_1992_b5_solution <-> putnam_1992_b5_bounded.
Admitted.

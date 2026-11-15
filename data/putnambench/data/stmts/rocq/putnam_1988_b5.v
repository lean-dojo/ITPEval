(* Statement-only formalization of PutnamBench corpus artifact putnam_1988_b5:
   the rank of the prescribed odd-dimensional skew-symmetric real matrix is
   twice the positive integer parameter. This file contains no proof. *)

From Stdlib Require Import Lists.List Arith.PeanoNat Vectors.Fin Reals ZArith.

Import ListNotations.
Open Scope R_scope.

Definition putnam_1988_b5_matrix (n : nat) : Type :=
  Fin.t n -> Fin.t n -> R.

Fixpoint putnam_1988_b5_sum (xs : list R) : R :=
  match xs with
  | [] => 0
  | x :: rest => x + putnam_1988_b5_sum rest
  end.

Definition putnam_1988_b5_delete_nth
    {T : Type} (j : nat) (xs : list T) : list T :=
  firstn j xs ++ skipn (S j) xs.

Definition putnam_1988_b5_cofactor_sign (j : nat) : R :=
  if Nat.even j then 1 else -1.

Fixpoint putnam_1988_b5_det
    (n : nat) (M : list (list R)) {struct n} : R :=
  match n with
  | O => 1
  | S k =>
      match M with
      | [] => 0
      | row :: rows =>
          putnam_1988_b5_sum
            (map
              (fun j : nat =>
                putnam_1988_b5_cofactor_sign j *
                nth j row 0 *
                putnam_1988_b5_det k
                  (map (putnam_1988_b5_delete_nth j) rows))
              (seq 0 (S k)))
      end
  end.

Definition putnam_1988_b5_minor
    {n : nat}
    (M : putnam_1988_b5_matrix n)
    (rows cols : list (Fin.t n)) : list (list R) :=
  map (fun i => map (fun j => M i j) cols) rows.

Definition putnam_1988_b5_rank_at_least
    {n : nat} (M : putnam_1988_b5_matrix n) (k : nat) : Prop :=
  exists rows cols : list (Fin.t n),
    length rows = k /\
    length cols = k /\
    NoDup rows /\
    NoDup cols /\
    putnam_1988_b5_det k (putnam_1988_b5_minor M rows cols) <> 0.

Definition putnam_1988_b5_rank
    {n : nat} (M : putnam_1988_b5_matrix n) (k : nat) : Prop :=
  putnam_1988_b5_rank_at_least M k /\
  forall l : nat,
    (k < l)%nat ->
    ~ putnam_1988_b5_rank_at_least M l.

Definition putnam_1988_b5_index
    {n : nat} (i : Fin.t n) : Z :=
  Z.of_nat (proj1_sig (Fin.to_nat i)).

Definition putnam_1988_b5_solution (n : nat) : nat :=
  (2 * n)%nat.

Theorem putnam_1988_b5
    (n : nat)
    (hn : (0 < n)%nat)
    (Mn : putnam_1988_b5_matrix (2 * n + 1))
    (Mnskewsymm :
      forall i j : Fin.t (2 * n + 1),
        Mn i j = - Mn j i)
    (hMn1 :
      forall i j : Fin.t (2 * n + 1),
        (1 <= putnam_1988_b5_index i - putnam_1988_b5_index j)%Z /\
        (putnam_1988_b5_index i - putnam_1988_b5_index j
          <= Z.of_nat n)%Z ->
        Mn i j = 1)
    (hMnn1 :
      forall i j : Fin.t (2 * n + 1),
        (Z.of_nat n
          < putnam_1988_b5_index i - putnam_1988_b5_index j)%Z ->
        Mn i j = -1) :
  putnam_1988_b5_rank Mn (putnam_1988_b5_solution n).
Admitted.

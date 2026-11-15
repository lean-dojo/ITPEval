(* Statement-only formalization of PutnamBench artifact putnam_2005_b6:
   the parity-signed sum of reciprocals of one plus the fixed-point count
   over all permutations of n elements; this file contains no proof. *)

From Stdlib Require Import Reals Lists.List Arith.PeanoNat.

Import ListNotations.
Open Scope R_scope.

Fixpoint putnam_2005_b6_insert_everywhere
    (x : nat) (p : list nat) : list (list nat) :=
  match p with
  | [] => [[x]]
  | y :: ys =>
      (x :: y :: ys) ::
      map (fun q => y :: q)
        (putnam_2005_b6_insert_everywhere x ys)
  end.

Fixpoint putnam_2005_b6_permutations
    (n : nat) : list (list nat) :=
  match n with
  | O => [[]]
  | S k =>
      flat_map (putnam_2005_b6_insert_everywhere k)
        (putnam_2005_b6_permutations k)
  end.

Fixpoint putnam_2005_b6_count_less
    (x : nat) (p : list nat) : nat :=
  match p with
  | [] => O
  | y :: ys =>
      (if Nat.ltb y x then 1 else 0) +
      putnam_2005_b6_count_less x ys
  end.

Fixpoint putnam_2005_b6_inversions
    (p : list nat) : nat :=
  match p with
  | [] => O
  | x :: xs =>
      putnam_2005_b6_count_less x xs +
      putnam_2005_b6_inversions xs
  end.

Fixpoint putnam_2005_b6_fixed_from
    (i : nat) (p : list nat) : nat :=
  match p with
  | [] => O
  | x :: xs =>
      (if Nat.eqb x i then 1 else 0) +
      putnam_2005_b6_fixed_from (S i) xs
  end.

Definition putnam_2005_b6_sign (p : list nat) : R :=
  if Nat.even (putnam_2005_b6_inversions p) then 1 else -1.

Definition putnam_2005_b6_term (p : list nat) : R :=
  putnam_2005_b6_sign p /
  INR (S (putnam_2005_b6_fixed_from 0 p)).

Definition putnam_2005_b6_sum (n : nat) : R :=
  fold_right Rplus 0
    (map putnam_2005_b6_term
      (putnam_2005_b6_permutations n)).

Theorem putnam_2005_b6 :
  forall n : nat,
    (0 < n)%nat ->
    putnam_2005_b6_sum n =
      (-1) ^ (n + 1) * INR n / INR (n + 1).
Admitted.

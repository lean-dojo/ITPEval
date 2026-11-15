(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1188392
  (thousand-theorems__rocq__Q1188392), "Zeckendorf's theorem": Fibonacci
  summation is an equivalence between natural numbers and finite decreasing
  lists of nonconsecutive indices at least two. This file contains no proof.
*)

From Stdlib Require Import List Arith PeanoNat.

Fixpoint q1188392_fib_pair (n : nat) : nat * nat :=
  match n with
  | 0 => (0, 1)
  | S k =>
      let '(current, next) := q1188392_fib_pair k in
      (next, current + next)
  end.

Definition q1188392_fib (n : nat) : nat :=
  fst (q1188392_fib_pair n).

Fixpoint q1188392_sum_fib (indices : list nat) : nat :=
  match indices with
  | nil => 0
  | index :: rest =>
      q1188392_fib index + q1188392_sum_fib rest
  end.

Fixpoint q1188392_is_zeckendorf_rep
    (indices : list nat) : Prop :=
  match indices with
  | nil => True
  | first :: rest =>
      match rest with
      | nil => 2 <= first
      | second :: _ =>
          second + 2 <= first /\
          q1188392_is_zeckendorf_rep rest
      end
  end.

Theorem q1188392_zeckendorf_equiv :
  exists encode : nat -> list nat,
    (forall n : nat,
      q1188392_is_zeckendorf_rep (encode n)) /\
    (forall n : nat,
      q1188392_sum_fib (encode n) = n) /\
    (forall indices : list nat,
      q1188392_is_zeckendorf_rep indices ->
      encode (q1188392_sum_fib indices) = indices).
Admitted.

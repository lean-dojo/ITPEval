(* Statement-only formalization of PutnamBench corpus artifact putnam_1995_b3:
   the sum of determinants of the digit matrices of all positive n-squared-digit
   decimal integers, as a function of n. This file contains no proof. *)

From Stdlib Require Import ZArith List Arith.PeanoNat.

Import ListNotations.

Fixpoint putnam_1995_b3_insert_everywhere
    (x : nat) (xs : list nat) : list (list nat) :=
  match xs with
  | [] => [[x]]
  | y :: ys =>
      (x :: y :: ys) ::
      map (cons y) (putnam_1995_b3_insert_everywhere x ys)
  end.

Fixpoint putnam_1995_b3_permutations
    (xs : list nat) : list (list nat) :=
  match xs with
  | [] => [[]]
  | x :: ys =>
      flat_map (putnam_1995_b3_insert_everywhere x)
        (putnam_1995_b3_permutations ys)
  end.

Definition putnam_1995_b3_decimal_digits : list nat :=
  seq 0 10.

Fixpoint putnam_1995_b3_digit_words
    (k : nat) : list (list nat) :=
  match k with
  | O => [[]]
  | S k' =>
      flat_map
        (fun d => map (cons d) (putnam_1995_b3_digit_words k'))
        putnam_1995_b3_decimal_digits
  end.

Definition putnam_1995_b3_positive_digit_words
    (k : nat) : list (list nat) :=
  filter
    (fun ds => negb (Nat.eqb (hd 0 ds) 0))
    (putnam_1995_b3_digit_words k).

Fixpoint putnam_1995_b3_inversions_from
    (x : nat) (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | y :: ys =>
      (if Nat.ltb y x then 1 else 0) +
      putnam_1995_b3_inversions_from x ys
  end.

Fixpoint putnam_1995_b3_inversions
    (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: ys =>
      putnam_1995_b3_inversions_from x ys +
      putnam_1995_b3_inversions ys
  end.

Definition putnam_1995_b3_permutation_sign
    (p : list nat) : Z :=
  if Nat.even (putnam_1995_b3_inversions p) then 1%Z else (-1)%Z.

Fixpoint putnam_1995_b3_permutation_product
    (n : nat) (digits rows columns : list nat) : Z :=
  match rows, columns with
  | i :: is, j :: js =>
      (Z.of_nat (nth ((i * n + j)%nat) digits O) *
       putnam_1995_b3_permutation_product n digits is js)%Z
  | _, _ => 1%Z
  end.

Fixpoint putnam_1995_b3_zsum (xs : list Z) : Z :=
  match xs with
  | [] => 0%Z
  | x :: ys => (x + putnam_1995_b3_zsum ys)%Z
  end.

Definition putnam_1995_b3_determinant
    (n : nat) (digits : list nat) : Z :=
  putnam_1995_b3_zsum
    (map
      (fun p =>
        (putnam_1995_b3_permutation_sign p *
         putnam_1995_b3_permutation_product
           n digits (seq 0 n) p)%Z)
      (putnam_1995_b3_permutations (seq 0 n))).

Definition putnam_1995_b3_determinant_sum (n : nat) : Z :=
  putnam_1995_b3_zsum
    (map
      (putnam_1995_b3_determinant n)
      (putnam_1995_b3_positive_digit_words (n * n))).

Definition putnam_1995_b3_solution (n : nat) : Z :=
  if Nat.eqb n 1 then 45%Z
  else if Nat.eqb n 2 then (10 * 45 ^ 2)%Z
  else 0%Z.

Theorem putnam_1995_b3
    (n : nat)
    (hn : (0 < n)%nat) :
  putnam_1995_b3_determinant_sum n =
  putnam_1995_b3_solution n.
Admitted.

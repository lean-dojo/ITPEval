From Coq Require Import Arith.PeanoNat.

Fixpoint putnam_2007_b1_eval
    (c : nat -> nat)
    (k x : nat) : nat :=
  match k with
  | O => c 0
  | S k' =>
      putnam_2007_b1_eval c k' x +
      c (S k') * x ^ (S k')
  end.

Theorem putnam_2007_b1
    (c : nat -> nat)
    (k : nat)
    (h_nonconstant :
      exists i : nat,
        (0 < i <= k)%nat /\ (c i > 0)%nat)
    (n : nat)
    (hn : (n > 0)%nat)
    (f : nat -> nat := putnam_2007_b1_eval c k) :
  Nat.divide (f n) (f (f n + 1)) <-> n = 1%nat.
Proof. Admitted.

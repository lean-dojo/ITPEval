(* Statement-only formalization of PutnamBench artifact putnam_1962_b1: the binomial identity for real falling factorials. This file contains no proof. *)

Require Import Reals Binomial.

Open Scope R_scope.

Fixpoint putnam_1962_b1_falling_product (x : R) (n : nat) : R :=
  match n with
  | O => 1
  | S m => putnam_1962_b1_falling_product x m * (x - INR m)
  end.

Fixpoint putnam_1962_b1_sum_upto (f : nat -> R) (n : nat) : R :=
  match n with
  | O => f O
  | S m => putnam_1962_b1_sum_upto f m + f (S m)
  end.

Theorem putnam_1962_b1
    (p : nat -> R -> R)
    (x y : R)
    (n : nat)
    (h0 : forall t : R, p O t = 1)
    (hp : forall (m : nat) (t : R),
        Nat.lt O m ->
        p m t = putnam_1962_b1_falling_product t m) :
    p n (x + y) =
      putnam_1962_b1_sum_upto
        (fun k : nat =>
          Binomial.C n k * p k x * p (Nat.sub n k) y)
        n.
Admitted.

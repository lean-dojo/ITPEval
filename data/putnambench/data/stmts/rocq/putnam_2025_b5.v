(* Statement-only formalization of PutnamBench corpus artifact putnam_2025_b5
   (putnambench__rocq__putnam_2025_b5): a lower bound for the number of
   descents among consecutive nonzero modular inverses modulo a prime greater
   than 3. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat QArith ZArith ZArith.Zcong.

Open Scope Q_scope.

Definition putnam_2025_b5_prime (p : nat) : Prop :=
  (2 <= p)%nat /\
  forall d : nat,
    Nat.divide d p ->
    d = 1%nat \/ d = p.

Definition putnam_2025_b5_mod_inv (p k : nat) : nat :=
  Z.to_nat (Z.invmod (Z.of_nat k) (Z.of_nat p)).

Fixpoint putnam_2025_b5_descent_count_from
    (p k remaining : nat) : nat :=
  match remaining with
  | O => O
  | S rest =>
      ((if Nat.ltb
          (putnam_2025_b5_mod_inv p (S k))
          (putnam_2025_b5_mod_inv p k)
        then 1
        else 0) +
       putnam_2025_b5_descent_count_from p (S k) rest)%nat
  end.

Definition putnam_2025_b5_descent_count (p : nat) : nat :=
  putnam_2025_b5_descent_count_from p 1%nat (p - 2)%nat.

Theorem putnam_2025_b5
    (p : nat)
    (hp_prime : putnam_2025_b5_prime p)
    (hp_gt : (3 < p)%nat) :
  (inject_Z (Z.of_nat p) / 4 - 1 <
   inject_Z (Z.of_nat (putnam_2025_b5_descent_count p)))%Q.
Admitted.

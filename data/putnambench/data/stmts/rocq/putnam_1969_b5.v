Section putnam_1969_b5.
Require Import Reals Finite_sets. From Coquelicot Require Import Coquelicot.
Open Scope R.

Theorem putnam_1969_b5
    (a : nat -> nat)
    (ha : forall n : nat, (0 < a n < a (Nat.add n 1))%nat)
    (hinvasum : ex_finite_lim_seq (fun n => sum_n (fun i => 1 / INR (a i)) n))
    (k : nat -> nat)
    (hk : forall x : nat, cardinal nat (fun n => (a n <= x)%nat) (k x))
    : is_lim_seq (fun t : nat => INR (k t) / INR t) 0.
Proof. Admitted.
End putnam_1969_b5.

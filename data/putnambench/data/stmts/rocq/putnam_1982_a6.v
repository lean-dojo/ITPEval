Require Import Nat Reals ZArith Coquelicot.Coquelicot.
Open Scope R.
Definition putnam_1982_a6_solution := False.

Definition putnam_1982_a6_positive_bijection (b : nat -> nat) : Prop :=
  (forall n : nat, (0 < n)%nat -> (0 < b n)%nat) /\
  (forall i j : nat,
    (0 < i)%nat ->
    (0 < j)%nat ->
    b i = b j ->
    i = j) /\
  (forall y : nat,
    (0 < y)%nat ->
    exists x : nat, (0 < x)%nat /\ b x = y).

Theorem putnam_1982_a6
    : (forall (b : nat -> nat) (a : nat -> R),
        putnam_1982_a6_positive_bijection b ->
        (forall i j : nat,
          (0 < i < j)%nat ->
          Rabs (a i) > Rabs (a j)) ->
        is_lim_seq
          (fun n => sum_n_m a 1 n)
          1 ->
        is_lim_seq
          (fun n =>
            Rabs (IZR (Z.of_nat (b n) - Z.of_nat n)) * Rabs (a n))
          0 ->
        is_lim_seq
          (fun n => sum_n_m (fun k => a (b k)) 1 n)
          1) <-> putnam_1982_a6_solution.
Proof. Admitted.

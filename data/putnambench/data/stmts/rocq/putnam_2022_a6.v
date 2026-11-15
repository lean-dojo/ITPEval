Require Import Nat Reals Coquelicot.Hierarchy.

Definition putnam_2022_a6_solution := fun n : nat => n.

Theorem putnam_2022_a6
    (N : nat)
    (hN : (0 < N)%nat)
    (M : nat)
    (sumIntervals : (nat -> R) -> nat -> R := fun s k =>
      sum_n
        (fun i =>
          (s ((2 * i + 1)%nat)) ^ ((2 * k - 1)%nat) -
          (s ((2 * i)%nat)) ^ ((2 * k - 1)%nat))
        ((N - 1)%nat))
    (valid : nat -> (nat -> R) -> Prop := fun m s =>
      forall k : nat,
        (1 <= k <= m)%nat ->
        sumIntervals s k = 1)
    (hvalid : nat -> Prop := fun m =>
      exists s : nat -> R,
        -1 < s 0%nat /\
        s ((2 * N - 1)%nat) < 1 /\
        (forall i : nat,
          Nat.lt i (Nat.sub (Nat.mul 2 N) 1) -> s i < s (S i)) /\
        valid m s)
    (hM : hvalid M)
    (hMub : forall m : nat, hvalid m -> le m M)
    : M = putnam_2022_a6_solution N.
Proof. Admitted. 

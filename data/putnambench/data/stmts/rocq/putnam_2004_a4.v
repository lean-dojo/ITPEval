Require Import List Reals QArith Coquelicot.Coquelicot.
Theorem putnam_2004_a4
    (n : nat)
    (avals : nat -> (nat -> nat -> R) -> Prop := fun (N : nat) (a : nat -> nat -> R) => forall i j : nat, lt i N /\ lt j n -> a i j = -1 \/ a i j = 0 \/ a i j = 1)
    (npos : gt n 0)
    : exists (N : nat) (c : nat -> Q) (a : nat -> nat -> R),
      gt N 0 /\
      avals N a /\
      forall x : list R,
        length x = n ->
        fold_left Rmult x 1 =
        sum_n
          (fun i : nat =>
            Q2R (c i) *
            (sum_n (fun j : nat => a i j * nth j x 0) (n - 1)) ^ n)
          (N - 1).
Proof. Admitted.

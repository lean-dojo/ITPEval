From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

Variable R : realType.
Theorem putnam_1962_b5
    (n : nat)
    (ng1 : gt n 1)
    (sumf : nat -> R := fun N =>
      \sum_(1%nat <= i < N.+1) (((i%:R : R) / (N%:R : R)) ^+ N))
    : ((3%:R : R) * n%:R + (1%:R : R)) /
        ((2%:R : R) * n%:R + (2%:R : R)) < sumf n < (2%:R : R).
Proof. Admitted.

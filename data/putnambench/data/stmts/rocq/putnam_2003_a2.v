From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals exp sequences normedtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Variable R : realType.

Definition putnam_2003_a2_nth_root (n : nat) (x : R) : R :=
  if x == 0 then 0 else expR (ln x * (1 / n%:R)).

Theorem putnam_2003_a2
    (n : nat)
    (hn : gt n 0)
    (a b : 'I_n -> R)
    (abnneg : forall i : 'I_n, (a i) >= 0 /\ (b i) >= 0)
    : putnam_2003_a2_nth_root n (\prod_(i < n) (a i)) +
      putnam_2003_a2_nth_root n (\prod_(i < n) (b i)) <=
      putnam_2003_a2_nth_root n (\prod_(i < n) (a i + b i)).
Proof. Admitted.

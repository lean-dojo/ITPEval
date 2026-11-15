Require Import Nat.

Definition putnam_2001_a5_property (a n : nat) : Prop :=
  a > 0 /\ n > 0 /\ a ^ (n + 1) - (a + 1) ^ n = 2001.

Theorem putnam_2001_a5 :
  exists a n : nat,
    putnam_2001_a5_property a n /\
    forall a' n' : nat,
      putnam_2001_a5_property a' n' ->
      a' = a /\ n' = n.
Proof. Admitted.

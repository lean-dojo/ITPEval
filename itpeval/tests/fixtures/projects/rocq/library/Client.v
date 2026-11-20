From ITPProject Require Import Library.
Theorem identity_nat (n : nat) : M.identity nat n = n.
Proof. apply M.identity_eq. Qed.

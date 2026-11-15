Require Import List Nat ZArith.

Definition putnam_1998_b4_solution (m n : nat) : Prop :=
  forall m2 n2 : nat,
    (m mod (2 ^ m2) = 0%nat /\
     m mod (2 ^ (m2 + 1)) <> 0%nat /\
     n mod (2 ^ n2) = 0%nat /\
     n mod (2 ^ (n2 + 1)) <> 0%nat) ->
    m2 <> n2.

Definition putnam_1998_b4_term (m n i : nat) : Z :=
  if Nat.even (i / m + i / n) then 1%Z else (-1)%Z.

Definition putnam_1998_b4_sum (m n : nat) : Z :=
  List.fold_right Z.add 0%Z
    (List.map (putnam_1998_b4_term m n) (List.seq 0 (m * n))).

Theorem putnam_1998_b4
    (hsum : nat -> nat -> Z := putnam_1998_b4_sum) :
  forall m n : nat,
    (m > 0 /\ n > 0)%nat ->
    (hsum m n = 0%Z <-> putnam_1998_b4_solution m n).
Proof. Admitted.

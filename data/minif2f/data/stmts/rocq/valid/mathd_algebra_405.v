Require Import Arith.

Theorem mathd_algebra_405 :
  (* The biconditional states that 1 and 2 are exactly the positive
     natural solutions, not merely an upper containment. *)
  forall x : nat,
    (0 < x /\ x^2 + 4 * x + 4 < 20) <-> (x = 1 \/ x = 2).
Proof.
Admitted.

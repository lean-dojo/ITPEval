Require Import QArith.

Open Scope Q_scope.

(* Q is not definitionally normalized, so denominators are read from
   canonical representatives on both sides. *)
Theorem numbertheory_xsqpysqintdenomeq :
  forall x y : Q,
    Qden (Qred (x * x + y * y)) = 1%positive ->
    Qden (Qred x) = Qden (Qred y).
Proof.
Admitted.

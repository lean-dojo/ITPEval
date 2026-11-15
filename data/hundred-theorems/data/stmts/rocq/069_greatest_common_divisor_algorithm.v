From Stdlib Require Import ZArith.

Open Scope Z_scope.

(**
  Rocq's executable extended Euclidean algorithm returns coefficients for
  Bézout's identity together with the standard gcd.
*)
Theorem extended_euclidean_algorithm_correct (a b : Z) :
  let '(u, v, d) := Z.extgcd a b in
  u * a + v * b = d /\ d = Z.gcd a b.
Proof.
  destruct (Z.extgcd a b) as [[u v] d] eqn:Hextgcd.
  exact (Z.extgcd_correct a b Hextgcd).
Qed.

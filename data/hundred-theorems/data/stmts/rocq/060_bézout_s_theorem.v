From Stdlib Require Import ZArith.

Open Scope Z_scope.

(**
  Bézout's identity over the integers, with the standard nonnegative gcd
  chosen by [Z.gcd].
*)
Theorem Bezout_gcd (a b : Z) :
  exists u v : Z, u * a + v * b = Z.gcd a b.
Proof.
  destruct (Z.extgcd a b) as [[u v] d] eqn:Hextgcd.
  pose proof (Z.extgcd_correct a b Hextgcd) as [Hlinear Hgcd].
  exists u, v.
  now rewrite Hlinear, Hgcd.
Qed.

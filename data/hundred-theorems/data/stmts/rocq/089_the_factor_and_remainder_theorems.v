(*
  The polynomial remainder and factor theorems over a field, stated using
  MathComp's polynomial division API.
*)

From mathcomp Require Import all_ssreflect all_algebra.

Import GRing.Theory.
Local Open Scope ring_scope.

Section FactorAndRemainder.

Variable F : fieldType.

Theorem polynomial_remainder_theorem (p : {poly F}) (c : F) :
  p %% ('X - c%:P) = p.[c]%:P.
Proof.
exact: modp_XsubC.
Qed.

Theorem polynomial_factor_theorem (p : {poly F}) (c : F) :
  reflect (p.[c] = 0) (('X - c%:P) %| p).
Proof.
exact: polyXsubCP.
Qed.

Theorem polynomial_root_factor_theorem (p : {poly F}) (c : F) :
  root p c = (('X - c%:P) %| p).
Proof.
exact: root_factor_theorem.
Qed.

End FactorAndRemainder.

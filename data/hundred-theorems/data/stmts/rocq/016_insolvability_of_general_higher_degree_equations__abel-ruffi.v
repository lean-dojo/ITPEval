(*
  Abel-Ruffini, stated through the maintained Abel formalization.  The
  concrete quintic below has Galois group S_5 and is therefore not solvable
  by radicals.
*)

From Abel Require Import abel.

Import GRing.Theory.
Local Open Scope ring_scope.

Theorem abel_ruffini :
  ~ solvable_by_radical_poly
      ('X^5 - 4 *: 'X + 2 : {poly rat}).
Proof.
exact: example_not_solvable_by_radicals.
Qed.

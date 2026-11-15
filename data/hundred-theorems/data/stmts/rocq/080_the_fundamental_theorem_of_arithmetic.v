(* Every positive natural number has a canonical prime-power decomposition. *)
From mathcomp Require Import all_ssreflect.

Theorem fundamental_theorem_of_arithmetic_decomposition n :
  0 < n ->
  n = \prod_(f <- prime_decomp n) f.1 ^ f.2.
Proof.
exact: prod_prime_decomp.
Qed.

(* The multiplicity of every prime uniquely determines a positive integer. *)
Theorem fundamental_theorem_of_arithmetic_uniqueness m n :
  0 < m ->
  0 < n ->
  (forall p, logn p m = logn p n) ->
  m = n.
Proof.
move=> Hm Hn Hlog.
exact: (eqn_from_log Hm Hn Hlog).
Qed.

Check fundamental_theorem_of_arithmetic_decomposition.
Check fundamental_theorem_of_arithmetic_uniqueness.

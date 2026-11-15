(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.let_clause_1078 (catalog title "div_mod.let_clause_1078"):
  two natural-number quotient-remainder specifications, their explicit
  remainder bounds and decomposition equations, and ordered quotients imply
  the first decomposition with commuted addition and multiplication. This
  file contains no proof.
*)

Inductive div_mod_spec (n m q r : nat) : Prop :=
| div_mod_spec_case :
    r < m ->
    n = q * m + r ->
    div_mod_spec n m q r.

Theorem div_mod_let_clause_1078 :
  forall a b q r q1 r1 : nat,
    div_mod_spec a b q r ->
    r < b ->
    a = q * b + r ->
    div_mod_spec a b q1 r1 ->
    r1 < b ->
    a = q1 * b + r1 ->
    q <= q1 ->
    q < q1 ->
    a = r + b * q.
Admitted.

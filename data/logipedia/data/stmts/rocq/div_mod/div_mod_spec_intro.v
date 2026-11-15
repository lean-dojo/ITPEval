(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.div_mod_spec_intro (catalog title
  "div_mod.div_mod_spec_intro"): natural numbers satisfying the remainder
  bound and quotient-remainder equation satisfy the division specification.
  This file contains no proof.
*)

Inductive div_mod_spec (n m q r : nat) : Prop :=
| div_mod_spec_case :
    r < m ->
    n = q * m + r ->
    div_mod_spec n m q r.

Theorem div_mod_div_mod_spec_intro :
  forall n m q r : nat,
    r < m ->
    n = q * m + r ->
    div_mod_spec n m q r.
Admitted.

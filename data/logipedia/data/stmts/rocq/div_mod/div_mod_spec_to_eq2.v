(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.div_mod_spec_to_eq2 (catalog title
  "div_mod.div_mod_spec_to_eq2"): the remainder component is unique among
  natural-number pairs satisfying the division specification's remainder
  bound and quotient-remainder equation. This file contains no proof.
*)

Inductive div_mod_spec (n m q r : nat) : Prop :=
| div_mod_spec_case :
    r < m ->
    n = q * m + r ->
    div_mod_spec n m q r.

Theorem div_mod_div_mod_spec_to_eq2 :
  forall a b q r q1 r1 : nat,
    div_mod_spec a b q r ->
    div_mod_spec a b q1 r1 ->
    r = r1.
Admitted.

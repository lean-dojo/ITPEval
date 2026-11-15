(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.match_div_mod_spec_prop (catalog title
  "div_mod.match_div_mod_spec_prop"): the natural-number division
  specification eliminates into any proposition from its remainder-bound
  and quotient-remainder equation case. This file contains no proof.
*)

Inductive div_mod_spec (n m q r : nat) : Prop :=
| div_mod_spec_case :
    r < m ->
    n = q * m + r ->
    div_mod_spec n m q r.

Theorem div_mod_match_div_mod_spec_prop :
  forall (n m q r : nat) (return_ : Prop),
    (r < m -> n = q * m + r -> return_) ->
    div_mod_spec n m q r ->
    return_.
Admitted.

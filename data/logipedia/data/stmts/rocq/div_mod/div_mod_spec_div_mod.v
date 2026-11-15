(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.div_mod_spec_div_mod (catalog title
  "div_mod.div_mod_spec_div_mod"): for a positive natural divisor, the source
  fuel-recursive quotient and remainder satisfy the division specification.
  This file contains no proof.
*)

Fixpoint div_mod_source_div_aux (p n m : nat) {struct p} : nat :=
  match p with
  | O => O
  | S q =>
      if Nat.leb n m
      then O
      else S (div_mod_source_div_aux q (n - S m) m)
  end.

Fixpoint div_mod_source_mod_aux (p n m : nat) {struct p} : nat :=
  match p with
  | O => n
  | S q =>
      if Nat.leb n m
      then n
      else div_mod_source_mod_aux q (n - S m) m
  end.

Definition div_mod_source_div (n m : nat) : nat :=
  match m with
  | O => S n
  | S p => div_mod_source_div_aux n n p
  end.

Definition div_mod_source_mod (n m : nat) : nat :=
  match m with
  | O => n
  | S p => div_mod_source_mod_aux n n p
  end.

Inductive div_mod_spec (n m q r : nat) : Prop :=
| div_mod_spec_intro :
    r < m ->
    n = q * m + r ->
    div_mod_spec n m q r.

Theorem div_mod_div_mod_spec_div_mod :
  forall n m : nat,
    0 < m ->
    div_mod_spec
      n
      m
      (div_mod_source_div n m)
      (div_mod_source_mod n m).
Admitted.

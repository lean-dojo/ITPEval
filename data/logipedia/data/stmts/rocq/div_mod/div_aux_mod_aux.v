(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.div_aux_mod_aux (catalog title "div_mod.div_aux_mod_aux"):
  the fuel-indexed natural-number division and remainder auxiliaries
  decompose every dividend as quotient times the successor of the divisor
  parameter, plus the remainder. This file contains no proof.
*)

Fixpoint div_aux (p n m : nat) {struct p} : nat :=
  match p with
  | O => O
  | S q =>
      if Nat.leb n m
      then O
      else S (div_aux q (n - S m) m)
  end.

Fixpoint mod_aux (p n m : nat) {struct p} : nat :=
  match p with
  | O => n
  | S q =>
      if Nat.leb n m
      then n
      else mod_aux q (n - S m) m
  end.

Theorem div_mod_div_aux_mod_aux :
  forall p n m : nat,
    n = div_aux p n m * S m + mod_aux p n m.
Admitted.

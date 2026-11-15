(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.eq_times_div_minus_mod (catalog title
  "div_mod.eq_times_div_minus_mod"): for all natural numbers, the source
  fuel-recursive quotient times the divisor equals the dividend minus the
  source remainder. This file contains no proof.
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

Theorem div_mod_eq_times_div_minus_mod :
  forall a b : nat,
    div_mod_source_div a b * b =
    a - div_mod_source_mod a b.
Admitted.

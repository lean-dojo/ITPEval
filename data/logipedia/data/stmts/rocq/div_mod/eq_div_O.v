(*
  Statement-only formalization of Logipedia corpus artifact div_mod.eq_div_O
  (catalog title "div_mod.eq_div_O"): for natural numbers n less than m, the
  source fuel-recursive quotient of n by m is zero. This file contains no
  proof.
*)

Fixpoint div_mod_source_div_aux (p n m : nat) {struct p} : nat :=
  match p with
  | O => O
  | S q =>
      if Nat.leb n m
      then O
      else S (div_mod_source_div_aux q (n - S m) m)
  end.

Definition div_mod_source_div (n m : nat) : nat :=
  match m with
  | O => S n
  | S p => div_mod_source_div_aux n n p
  end.

Theorem div_mod_eq_div_O :
  forall n m : nat,
    n < m ->
    div_mod_source_div n m = O.
Admitted.

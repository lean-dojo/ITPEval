(*
  Statement-only formalization of Logipedia corpus artifact div_mod.div_times
  (catalog title "div_mod.div_times"): for natural numbers a and positive b,
  the source fuel-recursive quotient of a times b by b equals a. This file
  contains no proof.
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

Theorem div_mod_div_times :
  forall a b : nat,
    O < b ->
    div_mod_source_div (a * b) b = a.
Admitted.

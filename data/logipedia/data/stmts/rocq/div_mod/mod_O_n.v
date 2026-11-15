(*
  Statement-only formalization of Logipedia corpus artifact div_mod.mod_O_n
  (catalog title "div_mod.mod_O_n"): for every natural number n, the source
  fuel-recursive remainder of zero modulo n is zero. This file contains no
  proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Fixpoint div_mod_source_mod_aux (p n m : nat) {struct p} : nat :=
  match p with
  | O => n
  | S q =>
      if Nat.leb n m
      then n
      else div_mod_source_mod_aux q (n - S m) m
  end.

Definition div_mod_source_mod (n m : nat) : nat :=
  match m with
  | O => n
  | S p => div_mod_source_mod_aux n n p
  end.

Theorem div_mod_mod_O_n :
  forall n : nat,
    div_mod_source_mod O n = O.
Admitted.

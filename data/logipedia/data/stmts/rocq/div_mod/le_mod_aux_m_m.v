(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.le_mod_aux_m_m (catalog title "div_mod.le_mod_aux_m_m"):
  for all natural-number fuel bounds and inputs, if the input is at most the
  fuel bound, the source modulo auxiliary returns a value at most its modulus
  parameter. This file contains no proof.
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

Theorem div_mod_le_mod_aux_m_m :
  forall p n m : nat,
    n <= p ->
    div_mod_source_mod_aux p n m <= m.
Admitted.

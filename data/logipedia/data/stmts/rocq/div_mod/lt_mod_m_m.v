(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.lt_mod_m_m (catalog title "div_mod.lt_mod_m_m"): for all natural
  numbers n and positive moduli m, the source remainder of n modulo m is
  strictly less than m. This file contains no proof.
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

Theorem div_mod_lt_mod_m_m :
  forall n m : nat,
    0 < m ->
    div_mod_source_mod n m < m.
Admitted.

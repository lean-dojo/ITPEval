(*
  Statement-only formalization of Logipedia corpus artifact exp.lt_O_exp
  (catalog title "exp.lt_O_exp"): every natural power of a positive natural
  base is positive. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Fixpoint logipedia_exp (n m : nat) : nat :=
  match m with
  | O => S O
  | S k => Nat.mul (logipedia_exp n k) n
  end.

Theorem exp_lt_O_exp :
  forall n m : nat,
    0 < n ->
    0 < logipedia_exp n m.
Admitted.

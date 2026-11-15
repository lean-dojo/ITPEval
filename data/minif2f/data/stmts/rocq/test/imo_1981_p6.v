Require Import PeanoNat.

(*
  Statement-only formalization of miniF2F test problem imo_1981_p6:
  the Ackermann-style recurrence yields both the level-four recurrence and
  the requested power-tower value.
*)

Theorem imo_1981_p6
  (f : nat -> nat -> nat)
  (g : nat -> nat)
  (h0 : forall y, f 0 y = y + 1)
  (h1 : forall x, f (S x) 0 = f x 1)
  (h2 : forall x y, f (S x) (S y) = f x (f (S x) y))
  (h3 : g 0 = 2)
  (h4 : forall n, g (S n) = 2^(g n)) :
  (forall y, f 4 (S y) = 2^(f 4 y + 3) - 3) /\
  f 4 1981 = g 1983 - 3.
Proof.
Admitted.

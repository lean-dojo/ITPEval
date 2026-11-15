(*
  Statement-only formalization of Thousand Theorems corpus artifact Q853067
  (thousand-theorems__rocq__Q853067), "Solutions to Pell's equation": every
  natural-number solution of x^2 - (a^2 - 1)y^2 = 1 for a > 1 occurs in the
  recursively defined Pell sequence. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Module Pell.

Fixpoint pell
    (a : nat) (_a1 : (1 < a)%nat) (n : nat) : (nat * nat)%type :=
  match n with
  | O => (1, 0)
  | S m =>
      let '(x, y) := pell a _a1 m in
      (x * a + (a * a - 1) * y, x + y * a)
  end.

Definition xn
    (a : nat) (a1 : (1 < a)%nat) (n : nat) : nat :=
  fst (pell a a1 n).

Definition yn
    (a : nat) (a1 : (1 < a)%nat) (n : nat) : nat :=
  snd (pell a a1 n).

Theorem eq_pell :
  forall (a : nat) (a1 : (1 < a)%nat) (x y : nat),
    x * x - (a * a - 1) * y * y = 1 ->
    exists n : nat,
      x = xn a a1 n /\ y = yn a a1 n.
Admitted.

End Pell.

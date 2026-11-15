(*
  Statement-only formalization of Thousand Theorems corpus artifact Q16251580
  (thousand-theorems__rocq__Q16251580), "Matiyasevich's theorem": a system of
  natural-number Pell equations, congruences, and divisibility conditions
  characterizes the indexed Pell sequence. This file contains no proof.
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

Definition mod_eq (modulus left right : nat) : Prop :=
  match modulus with
  | O => left = right
  | S m => Nat.modulo left (S m) = Nat.modulo right (S m)
  end.

Theorem matiyasevic :
  forall a k x y : nat,
    (exists a1 : (1 < a)%nat,
        xn a a1 k = x /\ yn a a1 k = y) <->
    (1 < a)%nat /\
    (k <= y)%nat /\
    ((x = 1 /\ y = 0) \/
     exists u v s t b : nat,
       x * x - (a * a - 1) * y * y = 1 /\
       u * u - (a * a - 1) * v * v = 1 /\
       s * s - (b * b - 1) * t * t = 1 /\
       (1 < b)%nat /\
       mod_eq (4 * y) b 1 /\
       mod_eq u b a /\
       (0 < v)%nat /\
       Nat.divide (y * y) v /\
       mod_eq u s x /\
       mod_eq (4 * y) t k).
Admitted.

End Pell.

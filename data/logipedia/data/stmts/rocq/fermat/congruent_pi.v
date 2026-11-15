(*
  Statement-only formalization of Logipedia corpus artifact
  fermat.congruent_pi (catalog title "fermat.congruent_pi"): the product of
  finitely many natural numbers is congruent modulo a positive natural
  modulus to the product of their remainders. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Fixpoint fermat_product_prefix (f : nat -> nat) (n : nat) : nat :=
  match n with
  | O => 1
  | S k => f k * fermat_product_prefix f k
  end.

Definition fermat_mod (n p : nat) : nat :=
  match p with
  | O => n
  | S p' => Nat.modulo n (S p')
  end.

Definition fermat_congruent (n m p : nat) : Prop :=
  fermat_mod n p = fermat_mod m p.

Theorem congruent_pi :
  forall (f : nat -> nat) (n p : nat),
    0 < p ->
    fermat_congruent
      (fermat_product_prefix f n)
      (fermat_product_prefix (fun i => fermat_mod (f i) p) n)
      p.
Admitted.

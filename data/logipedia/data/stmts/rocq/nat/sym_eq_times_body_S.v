(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_times_body_S (catalog title "nat.sym_eq_times_body_S"): for every
  natural number, the function mapping m to m plus n times m is Leibniz-equal
  to the multiplication body at the successor of n. This file contains no
  proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Definition logipedia_times_body (n : nat) : nat -> nat :=
  match n with
  | O => fun _ : nat => O
  | S k => fun m : nat => Nat.add m (Nat.mul k m)
  end.

Theorem logipedia_nat_sym_eq_times_body_S :
  forall n : nat,
    logipedia_leibniz
      (nat -> nat)
      (fun m : nat => Nat.add m (Nat.mul n m))
      (logipedia_times_body (S n)).
Admitted.

(*
  Statement-only formalization of Logipedia corpus artifact
  fermat.permut_mod (catalog title "fermat.permut_mod"): multiplication by
  a natural number not divisible by a natural prime, followed by reduction
  modulo that prime, permutes the naturals from zero through the prime's
  predecessor. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition fermat_divides (n m : nat) : Prop :=
  exists q : nat, m = n * q.

Definition fermat_prime (p : nat) : Prop :=
  1 < p /\
  forall m : nat,
    fermat_divides m p ->
    1 < m ->
    m = p.

Definition fermat_mod (n p : nat) : nat :=
  match p with
  | O => n
  | S p' => Nat.modulo n (S p')
  end.

Definition fermat_injn (f : nat -> nat) (m : nat) : Prop :=
  forall i j : nat,
    i <= m ->
    j <= m ->
    f i = f j ->
    i = j.

Definition fermat_permut (f : nat -> nat) (m : nat) : Prop :=
  (forall i : nat, i <= m -> f i <= m) /\
  fermat_injn f m.

Theorem permut_mod :
  forall p a : nat,
    fermat_prime p ->
    ~ fermat_divides p a ->
    fermat_permut
      (fun n : nat => fermat_mod (a * n) p)
      (Nat.pred p).
Admitted.

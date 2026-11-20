From Stdlib Require Import Init.Nat.
From ITPProject Require Import StrictProp.
Module M.
Section Local.
Variable A : Type.
Definition identity (x : A) : A := x.
Theorem identity_eq (x : A) : identity x = x.
Proof. reflexivity. Qed.
End Local.
End M.

Lemma focus_shelf : (True /\ True) /\ True.
Proof.
  split.
  - split.
    + shelve.
    + exact I.
  - exact I.
  Unshelve. exact I.
Qed.

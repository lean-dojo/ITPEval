(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.same_bigop: two filtered finite folds are equal when their selection
  predicates agree below the bound and their selected values agree there.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat Bool.Bool.

Definition sameF_upto {A : Type}
    (k : nat) (f g : nat -> A) : Prop :=
  forall i : nat,
    i < k ->
    f i = g i.

Definition sameF_p {A : Type}
    (k : nat) (p : nat -> bool) (f g : nat -> A) : Prop :=
  forall i : nat,
    i < k ->
    p i = true ->
    f i = g i.

Fixpoint bigop {H : Type}
    (n : nat) (p : nat -> bool) (nil : H)
    (op : H -> H -> H) (f : nat -> H) : H :=
  match n with
  | O => nil
  | S k =>
      if p k
      then op (f k) (bigop k p nil op f)
      else bigop k p nil op f
  end.

Theorem bigops_same_bigop :
  forall (B : Type)
         (k : nat)
         (p1 p2 : nat -> bool)
         (nil : B)
         (op : B -> B -> B)
         (f g : nat -> B),
    sameF_upto k p1 p2 ->
    sameF_p k p1 f g ->
    bigop k p1 nil op f =
    bigop k p2 nil op g.
Admitted.

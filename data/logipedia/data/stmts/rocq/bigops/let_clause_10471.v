(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.let_clause_10471 (catalog title "bigops.let_clause_10471"):
  a let-clause proposition about an isomorphism of filtered finite products
  and the quotient-remainder identity on natural numbers. This file contains
  no proof.
*)

From Stdlib Require Import Arith.PeanoNat Bool.Bool.

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

Definition sub_hk
    (h k : nat -> nat) (n1 n2 : nat)
    (p1 p2 : nat -> bool) (f1 f2 : nat -> nat) : Prop :=
  forall i : nat,
    i < n1 ->
    p1 i = true ->
    (h i < n2 /\ p2 (h i) = true) /\ k (h i) = i.

Definition same_selected_values
    (n : nat) (p : nat -> bool)
    (f1 f2 h : nat -> nat) : Prop :=
  forall i : nat,
    i < n ->
    p i = true ->
    f1 i = f2 (h i).

Definition iso
    (n1 n2 : nat) (p1 p2 : nat -> bool)
    (f1 f2 : nat -> nat) : Prop :=
  exists h k : nat -> nat,
    (same_selected_values n1 p1 f1 f2 h /\
      sub_hk h k n1 n2 p1 p2 f1 f2) /\
    sub_hk k h n2 n1 p2 p1 f2 f1.

Definition source_div (n d : nat) : nat :=
  match d with
  | O => S n
  | S d' => Nat.div n (S d')
  end.

Definition source_mod (n d : nat) : nat :=
  match d with
  | O => n
  | S d' => Nat.modulo n (S d')
  end.

Theorem bigops_let_clause_10471 :
  forall (n1 n2 : nat)
         (p1 p2 : nat -> bool)
         (f1 f2 : nat -> nat),
    iso n1 n2 p1 p2 f1 f2 ->
    forall h : nat -> nat,
      (exists k : nat -> nat,
        (same_selected_values n1 p1 f1 f2 h /\
          sub_hk h k n1 n2 p1 p2 f1 f2) /\
        sub_hk k h n2 n1 p2 p1 f2 f1) ->
      forall k : nat -> nat,
        ((same_selected_values n1 p1 f1 f2 h /\
            sub_hk h k n1 n2 p1 p2 f1 f2) /\
          sub_hk k h n2 n1 p2 p1 f2 f1) ->
        (same_selected_values n1 p1 f1 f2 h /\
          sub_hk h k n1 n2 p1 p2 f1 f2) ->
        same_selected_values n1 p1 f1 f2 h ->
        forall i m : nat,
          (forall f : nat -> bool,
            0 <= n1 ->
            sub_hk h k 0 m p1 f f1 f2 ->
            sub_hk k h m 0 f p1 f2 f1 ->
            bigop 0 p1 1 Nat.mul f1 =
            bigop m f 1 Nat.mul f2) ->
          forall p20 : nat -> bool,
            0 <= n1 ->
            sub_hk h k 0 (S m) p1 p20 f1 f2 ->
            sub_hk k h (S m) 0 p20 p1 f2 f1 ->
            forall x2571 x2572 : nat,
              x2571 =
              Nat.add
                (Nat.mul x2572 (source_div x2571 x2572))
                (source_mod x2571 x2572).
Admitted.

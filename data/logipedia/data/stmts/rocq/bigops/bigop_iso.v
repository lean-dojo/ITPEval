(*
  Statement-only formalization of Logipedia corpus artifact bigops.bigop_iso:
  an index isomorphism preserving selected values leaves a filtered finite
  product unchanged. This file contains no proof.
*)

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

Definition iso
    (n1 n2 : nat) (p1 p2 : nat -> bool)
    (f1 f2 : nat -> nat) : Prop :=
  exists h k : nat -> nat,
    ((forall i : nat,
        i < n1 ->
        p1 i = true ->
        f1 i = f2 (h i)) /\
      sub_hk h k n1 n2 p1 p2 f1 f2) /\
    sub_hk k h n2 n1 p2 p1 f2 f1.

Theorem bigop_iso :
  forall (n1 n2 : nat)
         (p1 p2 : nat -> bool)
         (f1 f2 : nat -> nat),
    iso n1 n2 p1 p2 f1 f2 ->
    bigop n1 p1 1 Nat.mul f1 =
    bigop n2 p2 1 Nat.mul f2.
Admitted.

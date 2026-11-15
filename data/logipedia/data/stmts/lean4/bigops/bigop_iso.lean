-- Statement-only formalization of Logipedia corpus artifact "bigops.bigop_iso"
-- (catalog title "bigops.bigop_iso"): invariance of a Boolean-filtered finite
-- product of natural numbers under a value-preserving isomorphism of its selected
-- prefix indices. This file contains no proof.

namespace bigops

def bigop (H : Type) :
    Nat -> (Nat -> Bool) -> H -> (H -> H -> H) -> (Nat -> H) -> H
  | 0, _p, nil, _op, _f => nil
  | n + 1, p, nil, op, f =>
      match p n with
      | true => op (f n) (bigop H n p nil op f)
      | false => bigop H n p nil op f

def sub_hk
    (h k : Nat -> Nat) (n1 n2 : Nat) (p1 p2 : Nat -> Bool)
    (_f1 _f2 : Nat -> Nat) : Prop :=
  forall i : Nat, i < n1 -> p1 i = true ->
    (h i < n2 /\ p2 (h i) = true) /\ k (h i) = i

def iso
    (n1 n2 : Nat) (p1 p2 : Nat -> Bool) (f1 f2 : Nat -> Nat) : Prop :=
  exists h k : Nat -> Nat,
    ((forall i : Nat, i < n1 -> p1 i = true -> f1 i = f2 (h i)) /\
      sub_hk h k n1 n2 p1 p2 f1 f2) /\
    sub_hk k h n2 n1 p2 p1 f2 f1

theorem bigop_iso
    (n1 n2 : Nat) (p1 p2 : Nat -> Bool) (f1 f2 : Nat -> Nat)
    (hiso : iso n1 n2 p1 p2 f1 f2) :
    bigop Nat n1 p1 1 Nat.mul f1 = bigop Nat n2 p2 1 Nat.mul f2 := sorry

end bigops

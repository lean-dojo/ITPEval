-- Statement-only formalization of Logipedia corpus artifact "bigops.let_clause_10471"
-- (catalog title "bigops.let_clause_10471"): a let-clause induction step relating
-- Boolean-filtered finite products through inverse index maps and concluding the
-- natural-number quotient-remainder decomposition. This file contains no proof.

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

theorem let_clause_10471
    (n1 n2 : Nat) (p1 p2 : Nat -> Bool) (f1 f2 : Nat -> Nat)
    (hiso : iso n1 n2 p1 p2 f1 f2) :
    forall h : Nat -> Nat,
      (exists k : Nat -> Nat,
        (((forall i : Nat, i < n1 -> p1 i = true -> f1 i = f2 (h i)) /\
          sub_hk h k n1 n2 p1 p2 f1 f2) /\
        sub_hk k h n2 n1 p2 p1 f2 f1)) ->
      forall k : Nat -> Nat,
        (((forall i : Nat, i < n1 -> p1 i = true -> f1 i = f2 (h i)) /\
          sub_hk h k n1 n2 p1 p2 f1 f2) /\
        sub_hk k h n2 n1 p2 p1 f2 f1) ->
        ((forall i : Nat, i < n1 -> p1 i = true -> f1 i = f2 (h i)) /\
          sub_hk h k n1 n2 p1 p2 f1 f2) ->
        (forall i : Nat, i < n1 -> p1 i = true -> f1 i = f2 (h i)) ->
        forall _i m : Nat,
          (forall f : Nat -> Bool,
            0 <= n1 ->
            sub_hk h k 0 m p1 f f1 f2 ->
            sub_hk k h m 0 f p1 f2 f1 ->
            bigop Nat 0 p1 1 Nat.mul f1 = bigop Nat m f 1 Nat.mul f2) ->
          forall p20 : Nat -> Bool,
            0 <= n1 ->
            sub_hk h k 0 (m + 1) p1 p20 f1 f2 ->
            sub_hk k h (m + 1) 0 p20 p1 f2 f1 ->
            forall x2571 x2572 : Nat,
              x2571 = x2572 * Nat.div x2571 x2572 + Nat.mod x2571 x2572 := sorry

end bigops

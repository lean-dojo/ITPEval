-- Statement-only formalization of Logipedia corpus artifact "nat.eq_plus"
-- (catalog title "nat.eq_plus"): each partially applied natural-number addition
-- function is Leibniz-equal to its naturally filtered body. This file contains no proof.

namespace nat

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

def filterNatType (R : Type) (f : Nat → R) (n : Nat) : R :=
  f n

def plus : Nat → Nat → Nat
  | 0, m => m
  | Nat.succ n, m => Nat.succ (plus n m)

def plusBody : Nat → Nat → Nat
  | 0, m => m
  | Nat.succ n, m => Nat.succ (plus n m)

theorem eq_plus :
    ∀ n : Nat,
      Leibniz (Nat → Nat) (plus n)
        (filterNatType (Nat → Nat) plusBody n) := sorry

end nat

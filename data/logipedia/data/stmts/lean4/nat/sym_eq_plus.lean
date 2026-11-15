-- Statement-only formalization of Logipedia corpus artifact "nat.sym_eq_plus"
-- (catalog title "nat.sym_eq_plus"): at every natural argument, the
-- natural-type filter of the addition body is Leibniz-equal to the addition
-- function at the same argument. This file contains no proof.

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

theorem sym_eq_plus :
    ∀ n : Nat,
      Leibniz (Nat → Nat)
        (filterNatType (Nat → Nat) plusBody n)
        (plus n) := sorry

end nat

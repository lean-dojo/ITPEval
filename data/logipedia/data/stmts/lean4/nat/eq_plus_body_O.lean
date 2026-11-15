-- Statement-only formalization of Logipedia corpus artifact
-- "nat.eq_plus_body_O" (catalog title "nat.eq_plus_body_O"): Leibniz equality
-- relates the fixed recursive addition body at zero to the identity function on
-- natural numbers. This file contains no proof.

namespace nat

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

def plus : Nat → Nat → Nat
  | 0, m => m
  | Nat.succ n, m => Nat.succ (plus n m)

def plusBody : Nat → Nat → Nat
  | 0, m => m
  | Nat.succ n, m => Nat.succ (plus n m)

theorem eq_plus_body_O :
    Leibniz (Nat → Nat) (plusBody 0) (fun m ↦ m) := sorry

end nat

-- Statement-only formalization of Logipedia corpus artifact
-- "nat.sym_eq_plus_body_O" (catalog title "nat.sym_eq_plus_body_O"): Leibniz
-- equality relates the identity function on natural numbers to the zero case
-- of the recursive addition body. This file contains no proof.

namespace nat

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

def plus : Nat → Nat → Nat
  | 0, m => m
  | Nat.succ n, m => Nat.succ (plus n m)

def plusBody : Nat → Nat → Nat
  | 0, m => m
  | Nat.succ n, m => Nat.succ (plus n m)

theorem sym_eq_plus_body_O :
    Leibniz (Nat → Nat) (fun m ↦ m) (plusBody 0) := sorry

end nat

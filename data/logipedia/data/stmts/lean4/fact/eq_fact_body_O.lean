-- Statement-only formalization of Logipedia corpus artifact "fact.eq_fact_body_O"
-- (catalog title "fact.eq_fact_body_O"): Leibniz equality relates the fixed
-- factorial body at zero to the successor of zero. This file contains no proof.

namespace fact

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

def fact_body : Nat → Nat
  | 0 => Nat.succ 0
  | Nat.succ n => fact_body n * Nat.succ n

theorem eq_fact_body_O :
    Leibniz Nat (fact_body 0) (Nat.succ 0) := sorry

end fact

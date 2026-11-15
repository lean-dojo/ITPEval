-- Statement-only formalization of Logipedia corpus artifact
-- "nat.sym_eq_minus_body_S" (catalog title "nat.sym_eq_minus_body_S"):
-- Leibniz equality relates the natural-number eliminator with successor n as
-- its zero branch and subtraction by n as its successor branch to the
-- subtraction body at successor n. This file contains no proof.

def nat.matchNatType (returnType : Type) (caseO : returnType)
    (caseS : Nat → returnType) : Nat → returnType
  | 0 => caseO
  | Nat.succ n => caseS n

def nat.minus (n m : Nat) : Nat :=
  n - m

def nat.minusBody : Nat → Nat → Nat
  | 0, _ => 0
  | Nat.succ n, m =>
      nat.matchNatType Nat (Nat.succ n) (fun q ↦ nat.minus n q) m

theorem nat.sym_eq_minus_body_S :
    ∀ n : Nat, ∀ P : (Nat → Nat) → Prop,
      P (fun m ↦ nat.matchNatType Nat (Nat.succ n) (fun q ↦ nat.minus n q) m) →
      P (nat.minusBody (Nat.succ n)) := sorry

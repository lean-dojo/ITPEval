-- Statement-only formalization of Logipedia corpus artifact
-- "nat.eq_match_nat_type_S" (catalog title "nat.eq_match_nat_type_S"):
-- evaluating a polymorphic natural-number eliminator at a successor is
-- Leibniz-equal to the successor branch applied to its predecessor.
-- This file contains no proof.

def nat.matchNatType (returnType : Type) (caseO : returnType)
    (caseS : Nat → returnType) : Nat → returnType
  | 0 => caseO
  | Nat.succ n => caseS n

theorem nat.eq_match_nat_type_S :
    ∀ (returnType : Type) (caseO : returnType) (caseS : Nat → returnType)
      (n : Nat) (P : returnType → Prop),
      P (nat.matchNatType returnType caseO caseS (Nat.succ n)) →
      P (caseS n) := sorry

-- Statement-only formalization of Logipedia corpus artifact
-- "nat.eq_match_nat_type_O" (catalog title "nat.eq_match_nat_type_O"):
-- evaluating a polymorphic natural-number eliminator at zero is Leibniz-equal
-- to its zero-branch value. This file contains no proof.

def nat.matchNatType (returnType : Type) (caseO : returnType)
    (caseS : Nat → returnType) : Nat → returnType
  | 0 => caseO
  | Nat.succ n => caseS n

theorem nat.eq_match_nat_type_O :
    ∀ (returnType : Type) (caseO : returnType) (caseS : Nat → returnType)
      (P : returnType → Prop),
      P (nat.matchNatType returnType caseO caseS 0) →
      P caseO := sorry

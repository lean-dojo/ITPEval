-- Statement-only formalization of Logipedia corpus artifact
-- "nat.sym_eq_match_nat_type_S" (catalog title "nat.sym_eq_match_nat_type_S"):
-- the successor-branch value is Leibniz-equal to a polymorphic natural-number
-- eliminator evaluated at the corresponding successor. This file contains no proof.

def nat.matchNatType (returnType : Type) (caseO : returnType)
    (caseS : Nat → returnType) : Nat → returnType
  | 0 => caseO
  | Nat.succ n => caseS n

theorem nat.sym_eq_match_nat_type_S :
    ∀ (returnType : Type) (caseO : returnType) (caseS : Nat → returnType)
      (n : Nat) (P : returnType → Prop),
      P (caseS n) →
      P (nat.matchNatType returnType caseO caseS (Nat.succ n)) := sorry

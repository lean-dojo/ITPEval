-- Statement-only formalization of Logipedia corpus artifact
-- "nat.sym_eq_match_nat_type_O" (catalog title "nat.sym_eq_match_nat_type_O"):
-- the zero branch is Leibniz-equal to a polymorphic natural-number eliminator
-- evaluated at zero. This file contains no proof.

def nat.matchNatType (returnType : Type) (caseO : returnType)
    (caseS : Nat → returnType) : Nat → returnType
  | 0 => caseO
  | Nat.succ n => caseS n

theorem nat.sym_eq_match_nat_type_O :
    ∀ (returnType : Type) (caseO : returnType) (caseS : Nat → returnType)
      (P : returnType → Prop),
      P caseO →
      P (nat.matchNatType returnType caseO caseS 0) := sorry

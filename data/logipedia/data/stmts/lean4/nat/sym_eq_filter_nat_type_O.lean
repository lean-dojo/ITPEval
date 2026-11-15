-- Statement-only formalization of Logipedia corpus artifact
-- "nat.sym_eq_filter_nat_type_O" (catalog title "nat.sym_eq_filter_nat_type_O"):
-- applying a natural-indexed function at zero is Leibniz-equal to filtering
-- that function at zero. This file contains no proof.

namespace nat

def filterNatType (returnType : Type) (returnFn : Nat → returnType) : Nat → returnType
  | 0 => returnFn 0
  | Nat.succ n => returnFn (Nat.succ n)

theorem sym_eq_filter_nat_type_O :
    ∀ (returnType : Type) (returnFn : Nat → returnType)
      (P : returnType → Prop),
      P (returnFn 0) →
      P (filterNatType returnType returnFn 0) := sorry

end nat

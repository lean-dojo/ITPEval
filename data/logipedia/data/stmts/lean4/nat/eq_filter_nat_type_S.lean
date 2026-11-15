-- Statement-only formalization of Logipedia corpus artifact
-- "nat.eq_filter_nat_type_S" (catalog title "nat.eq_filter_nat_type_S"):
-- the fixed polymorphic filter on a natural-indexed function is Leibniz-equal
-- at a successor to direct application there. This file contains no proof.

namespace nat

def filterNatType (returnType : Type) (returnFn : Nat → returnType) : Nat → returnType
  | 0 => returnFn 0
  | Nat.succ n => returnFn (Nat.succ n)

theorem eq_filter_nat_type_S :
    ∀ (returnType : Type) (returnFn : Nat → returnType) (n : Nat)
      (P : returnType → Prop),
      P (filterNatType returnType returnFn (Nat.succ n)) →
      P (returnFn (Nat.succ n)) := sorry

end nat

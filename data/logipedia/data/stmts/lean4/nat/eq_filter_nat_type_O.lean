-- Statement-only formalization of Logipedia corpus artifact
-- "nat.eq_filter_nat_type_O" (catalog title "nat.eq_filter_nat_type_O"):
-- the concrete polymorphic filter on a natural-indexed function agrees at zero
-- with direct application of that function. This file contains no proof.

namespace nat

def filterNatType (returnType : Type) (returnFn : Nat → returnType) : Nat → returnType
  | 0 => returnFn 0
  | Nat.succ n => returnFn (Nat.succ n)

theorem eq_filter_nat_type_O :
    ∀ (returnType : Type) (returnFn : Nat → returnType),
      filterNatType returnType returnFn 0 = returnFn 0 := sorry

end nat

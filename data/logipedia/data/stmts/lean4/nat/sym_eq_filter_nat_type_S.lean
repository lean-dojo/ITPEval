-- Statement-only formalization of Logipedia corpus artifact
-- "nat.sym_eq_filter_nat_type_S" (catalog title "nat.sym_eq_filter_nat_type_S"):
-- applying a natural-indexed function at a successor is Leibniz-equal to filtering
-- that function at the same successor. This file contains no proof.

namespace nat

def filterNatType (returnType : Type) (returnFn : Nat -> returnType) : Nat -> returnType
  | 0 => returnFn 0
  | Nat.succ n => returnFn (Nat.succ n)

theorem sym_eq_filter_nat_type_S :
    forall (returnType : Type) (returnFn : Nat -> returnType) (n : Nat)
      (P : returnType -> Prop),
      P (returnFn (Nat.succ n)) ->
      P (filterNatType returnType returnFn (Nat.succ n)) := sorry

end nat

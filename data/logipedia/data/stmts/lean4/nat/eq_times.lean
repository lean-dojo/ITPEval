-- Statement-only formalization of Logipedia corpus artifact "nat.eq_times"
-- (catalog title "nat.eq_times"): each partially applied natural-number multiplication
-- function is Leibniz-equal to its naturally filtered body. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) -> (Nat -> R) -> Nat -> R

-- itpeval-source-signature: logipedia:nat.times as times
axiom times : Nat -> Nat -> Nat

-- itpeval-source-signature: logipedia:nat.times_body as timesBody
axiom timesBody : Nat -> Nat -> Nat

theorem eq_times :
    forall n : Nat, forall P : (Nat -> Nat) -> Prop,
      P (times n) ->
      P (filterNatType (Nat -> Nat) timesBody n) := sorry

end nat

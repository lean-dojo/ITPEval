-- Statement-only formalization of Logipedia corpus artifact "div_mod.div_times"
-- (catalog title "div_mod.div_times"): dividing a product of natural numbers by
-- its positive second factor using the source fuel-recursive quotient returns
-- the first factor. This file contains no proof.

namespace div_mod

def divAux : Nat -> Nat -> Nat -> Nat
  | 0, _n, _m => 0
  | Nat.succ p, n, m =>
      if n <= m then 0 else Nat.succ (divAux p (n - Nat.succ m) m)

def div (n m : Nat) : Nat :=
  match m with
  | 0 => Nat.succ n
  | Nat.succ p => divAux n n p

theorem div_times :
    forall a b : Nat, 0 < b -> div (a * b) b = a := sorry

end div_mod

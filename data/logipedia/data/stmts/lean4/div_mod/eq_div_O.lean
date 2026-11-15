-- Statement-only formalization of Logipedia corpus artifact "div_mod.eq_div_O"
-- (catalog title "div_mod.eq_div_O"): if one natural number is strictly smaller
-- than another, the source fuel-recursive quotient of the former by the latter
-- is zero. This file contains no proof.

namespace div_mod

def divAux : Nat -> Nat -> Nat -> Nat
  | 0, _n, _m => 0
  | Nat.succ p, n, m =>
      if n <= m then 0 else Nat.succ (divAux p (n - Nat.succ m) m)

def div (n m : Nat) : Nat :=
  match m with
  | 0 => Nat.succ n
  | Nat.succ p => divAux n n p

theorem eq_div_O :
    forall n m : Nat, n < m -> div n m = 0 := sorry

end div_mod

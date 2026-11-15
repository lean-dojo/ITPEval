-- Statement-only formalization of Logipedia corpus artifact
-- "div_mod.eq_times_div_minus_mod" (catalog title "div_mod.eq_times_div_minus_mod"):
-- the source fuel-recursive natural-number quotient times the divisor equals
-- the dividend minus the corresponding remainder. This file contains no proof.

namespace div_mod

def modAux : Nat -> Nat -> Nat -> Nat
  | 0, n, _m => n
  | Nat.succ p, n, m =>
      if n <= m then n else modAux p (n - Nat.succ m) m

def divAux : Nat -> Nat -> Nat -> Nat
  | 0, _n, _m => 0
  | Nat.succ p, n, m =>
      if n <= m then 0 else Nat.succ (divAux p (n - Nat.succ m) m)

def mod (n m : Nat) : Nat :=
  match m with
  | 0 => n
  | Nat.succ p => modAux n n p

def div (n m : Nat) : Nat :=
  match m with
  | 0 => Nat.succ n
  | Nat.succ p => divAux n n p

theorem eq_times_div_minus_mod :
    forall a b : Nat, div a b * b = a - mod a b := sorry

end div_mod

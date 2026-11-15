-- Statement-only formalization of Logipedia corpus artifact "div_mod.div_aux_mod_aux"
-- (catalog title "div_mod.div_aux_mod_aux"): the fuel-indexed division and modulus
-- auxiliaries decompose a natural number into quotient times the successor divisor
-- plus remainder. This file contains no proof.

namespace div_mod

def modAux : Nat → Nat → Nat → Nat
  | 0, n, _m => n
  | Nat.succ p, n, m =>
      if n ≤ m then n else modAux p (n - Nat.succ m) m

def divAux : Nat → Nat → Nat → Nat
  | 0, _n, _m => 0
  | Nat.succ p, n, m =>
      if n ≤ m then 0 else Nat.succ (divAux p (n - Nat.succ m) m)

theorem div_aux_mod_aux :
    ∀ p n m : Nat,
      n = divAux p n m * Nat.succ m + modAux p n m := sorry

end div_mod

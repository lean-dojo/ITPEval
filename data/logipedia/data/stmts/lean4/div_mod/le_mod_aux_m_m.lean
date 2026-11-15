-- Statement-only formalization of Logipedia corpus artifact "div_mod.le_mod_aux_m_m"
-- (catalog title "div_mod.le_mod_aux_m_m"): a fuel-indexed natural-number modulus
-- auxiliary is bounded by its modulus when the dividend is at most the fuel.
-- This file contains no proof.

namespace div_mod

def modAux : Nat → Nat → Nat → Nat
  | 0, n, _m => n
  | Nat.succ p, n, m =>
      if n ≤ m then n else modAux p (n - Nat.succ m) m

theorem le_mod_aux_m_m :
    ∀ p n m : Nat, n ≤ p → modAux p n m ≤ m := sorry

end div_mod

-- Statement-only formalization of Logipedia corpus artifact "div_mod.lt_mod_m_m"
-- (catalog title "div_mod.lt_mod_m_m"): the source fuel-recursive natural-number
-- remainder modulo a positive modulus is strictly smaller than that modulus.
-- This file contains no proof.

namespace div_mod

def modAux : Nat -> Nat -> Nat -> Nat
  | 0, n, _m => n
  | Nat.succ p, n, m =>
      if n <= m then n else modAux p (n - Nat.succ m) m

def mod (n m : Nat) : Nat :=
  match m with
  | 0 => n
  | Nat.succ p => modAux n n p

theorem lt_mod_m_m :
    forall n m : Nat, 0 < m -> mod n m < m := sorry

end div_mod

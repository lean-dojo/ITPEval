-- Statement-only formalization of Logipedia corpus artifact "div_mod.mod_O_n"
-- (catalog title "div_mod.mod_O_n"): the source fuel-recursive natural-number
-- remainder of zero by every natural modulus is zero. This file contains no proof.

namespace div_mod

def modAux : Nat -> Nat -> Nat -> Nat
  | 0, n, _m => n
  | Nat.succ p, n, m =>
      if n <= m then n else modAux p (n - Nat.succ m) m

def mod (n m : Nat) : Nat :=
  match m with
  | 0 => n
  | Nat.succ p => modAux n n p

theorem mod_O_n :
    forall n : Nat, mod 0 n = 0 := sorry

end div_mod

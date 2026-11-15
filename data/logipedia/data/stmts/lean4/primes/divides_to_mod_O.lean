-- Statement-only formalization of Logipedia corpus artifact
-- "primes.divides_to_mod_O" (catalog title "primes.divides_to_mod_O"): a
-- positive natural divisor makes the source fuel-recursive remainder equal
-- to zero. This file contains no proof.

namespace div_mod

def modAux : Nat → Nat → Nat → Nat
  | 0, n, _m => n
  | Nat.succ p, n, m =>
      if n ≤ m then n else modAux p (n - Nat.succ m) m

def mod (n m : Nat) : Nat :=
  match m with
  | 0 => n
  | Nat.succ p => modAux n n p

end div_mod

namespace primes

def divides (n m : Nat) : Prop :=
  ∃ q : Nat, m = n * q

theorem divides_to_mod_O :
    ∀ n m : Nat, 0 < n → divides n m → div_mod.mod m n = 0 := sorry

end primes

-- Statement-only formalization of Logipedia corpus artifact
-- "primes.mod_O_to_divides" (catalog title "primes.mod_O_to_divides"): a
-- positive natural divisor divides any natural number whose source
-- fuel-recursive remainder modulo that divisor is zero. This file contains no proof.

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

theorem mod_O_to_divides :
    ∀ n m : Nat, 0 < n → div_mod.mod m n = 0 → divides n m := sorry

end primes

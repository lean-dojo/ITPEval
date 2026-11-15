-- Statement-only formalization of Logipedia corpus artifact
-- "primes.eq_mod_to_divides" (catalog title "primes.eq_mod_to_divides"):
-- equal remainders modulo a positive natural number imply that the modulus
-- divides the truncated natural-number difference. This file contains no proof.

namespace div_mod

def modAux : Nat -> Nat -> Nat -> Nat
  | 0, n, _m => n
  | Nat.succ p, n, m =>
      if n <= m then n else modAux p (n - Nat.succ m) m

def mod (n m : Nat) : Nat :=
  match m with
  | 0 => n
  | Nat.succ p => modAux n n p

end div_mod

namespace primes

def divides (n m : Nat) : Prop :=
  exists q : Nat, m = n * q

theorem eq_mod_to_divides :
    forall n m q : Nat,
      0 < q ->
      div_mod.mod n q = div_mod.mod m q ->
      divides q (n - m) := sorry

end primes

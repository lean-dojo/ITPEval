-- Statement-only formalization of Logipedia corpus artifact
-- "primes.divides_to_div_mod_spec" (catalog title
-- "primes.divides_to_div_mod_spec"): a positive natural divisor yields a
-- division specification with the source fuel-recursive quotient and zero
-- remainder. This file contains no proof.

namespace div_mod

def divAux : Nat -> Nat -> Nat -> Nat
  | 0, _n, _m => 0
  | Nat.succ p, n, m =>
      if n <= m then 0 else Nat.succ (divAux p (n - Nat.succ m) m)

def div (n m : Nat) : Nat :=
  match m with
  | 0 => Nat.succ n
  | Nat.succ p => divAux n n p

def div_mod_spec (n m q r : Nat) : Prop :=
  r < m /\ n = q * m + r

end div_mod

namespace primes

def divides (n m : Nat) : Prop :=
  exists q : Nat, m = n * q

theorem divides_to_div_mod_spec :
    forall n m : Nat,
      0 < n ->
      divides n m ->
      div_mod.div_mod_spec m n (div_mod.div m n) 0 := sorry

end primes

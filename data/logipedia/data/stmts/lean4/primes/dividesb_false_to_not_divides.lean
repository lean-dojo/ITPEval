-- Statement-only formalization of Logipedia corpus artifact
-- "primes.dividesb_false_to_not_divides" (catalog title
-- "primes.dividesb_false_to_not_divides"): a false result from the source
-- Boolean divisibility test rules out divisibility of natural numbers. This
-- file contains no proof.

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

def natEqb : Nat -> Nat -> Bool
  | 0, 0 => true
  | 0, Nat.succ _ => false
  | Nat.succ _, 0 => false
  | Nat.succ m, Nat.succ n => natEqb m n

def dividesb (n m : Nat) : Bool :=
  natEqb (div_mod.mod m n) 0

theorem dividesb_false_to_not_divides :
    forall n m : Nat, dividesb n m = false -> (divides n m -> False) := sorry

end primes

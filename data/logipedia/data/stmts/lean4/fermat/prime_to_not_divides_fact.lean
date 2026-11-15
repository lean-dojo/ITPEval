-- Statement-only formalization of Logipedia corpus artifact
-- "fermat.prime_to_not_divides_fact" (catalog title
-- "fermat.prime_to_not_divides_fact"): a prime natural number does not divide
-- the factorial of any smaller natural number. This file contains no proof.

namespace fermat

def divides (a b : Nat) : Prop :=
  ∃ q : Nat, b = a * q

def prime (p : Nat) : Prop :=
  1 < p ∧ ∀ m : Nat, divides m p → 1 < m → m = p

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)

theorem prime_to_not_divides_fact :
    ∀ p : Nat, prime p → ∀ n : Nat, n < p → ¬divides p (factorial n) := sorry

end fermat

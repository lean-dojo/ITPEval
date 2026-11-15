-- Statement-only formalization of Logipedia corpus artifact
-- "fermat.permut_mod" (catalog title "fermat.permut_mod"): multiplication by
-- a natural not divisible by a prime, followed by reduction modulo that prime,
-- permutes the natural numbers from zero through the predecessor of the prime.
-- This file contains no proof.

namespace fermat

def divides (n m : Nat) : Prop :=
  ∃ q : Nat, m = n * q

def prime (n : Nat) : Prop :=
  1 < n ∧ ∀ m : Nat, divides m n → 1 < m → m = n

def injn (f : Nat → Nat) (n : Nat) : Prop :=
  ∀ i j : Nat, i ≤ n → j ≤ n → f i = f j → i = j

def permut (f : Nat → Nat) (n : Nat) : Prop :=
  (∀ i : Nat, i ≤ n → f i ≤ n) ∧ injn f n

theorem permut_mod :
    ∀ p a : Nat, prime p → ¬divides p a →
      permut (fun n : Nat => (a * n) % p) (Nat.pred p) := sorry

end fermat

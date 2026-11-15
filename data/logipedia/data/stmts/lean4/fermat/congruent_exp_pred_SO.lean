-- Statement-only formalization of Logipedia corpus artifact
-- "fermat.congruent_exp_pred_SO" (catalog title "fermat.congruent_exp_pred_SO"):
-- Fermat's little theorem in congruence form for a prime natural modulus and
-- a base not divisible by that prime. This file contains no proof.

namespace fermat

def divides (n m : Nat) : Prop :=
  ∃ q : Nat, m = n * q

def prime (n : Nat) : Prop :=
  1 < n ∧ ∀ m : Nat, divides m n → 1 < m → m = n

def congruent (n m p : Nat) : Prop :=
  n % p = m % p

theorem congruent_exp_pred_SO :
    ∀ p a : Nat, prime p → ¬divides p a → congruent (a ^ Nat.pred p) 1 p := sorry

end fermat

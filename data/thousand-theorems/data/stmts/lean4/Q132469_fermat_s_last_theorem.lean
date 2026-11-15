-- Statement-only formalization of Thousand Theorems artifact Q132469
-- (thousand-theorems__lean4__Q132469), "Fermat's Last Theorem": for every
-- natural exponent at least three, the Fermat equation has no solution in
-- three nonzero natural numbers. This file contains no proof.

module

public import Init

@[expose] public section

namespace Q132469

/-- Fermat's Last Theorem over the natural numbers. -/
theorem fermat_last_theorem_statement :
    ∀ n : Nat, Nat.le (Nat.succ (Nat.succ (Nat.succ Nat.zero))) n →
      ∀ a b c : Nat, a ≠ Nat.zero → b ≠ Nat.zero → c ≠ Nat.zero →
        Nat.add (Nat.pow a n) (Nat.pow b n) ≠ Nat.pow c n := sorry

end Q132469

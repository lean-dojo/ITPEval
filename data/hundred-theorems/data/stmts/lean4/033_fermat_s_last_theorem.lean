-- Statement-only formalization of "Fermat's Last Theorem" from Hundred Theorems item 033.
-- It states that no positive natural numbers satisfy a^n + b^n = c^n for any natural
-- exponent n > 2. This file contains no proof.

namespace Theorems100

/-- Fermat's Last Theorem over positive natural numbers. -/
theorem fermat_last_theorem (n : Nat) (hn : n > 2) :
    ¬ ∃ a b c : Nat,
      0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ n + b ^ n = c ^ n := sorry

end Theorems100

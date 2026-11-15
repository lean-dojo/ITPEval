-- Statement-only formalization of Thousand Theorems artifact Q1082910
-- (thousand-theorems__lean4__Q1082910), "Euler's partition theorem": for every
-- natural number, the number of partitions into odd parts equals the number of
-- partitions into distinct parts. This file contains no proof.

module

public import Mathlib.Combinatorics.Enumerative.Partition.GenFun

@[expose] public section

namespace Q1082910

/-- Euler's partition theorem. -/
theorem card_odds_eq_card_distincts (n : ℕ) :
    (Nat.Partition.odds n).card = (Nat.Partition.distincts n).card := sorry

end Q1082910

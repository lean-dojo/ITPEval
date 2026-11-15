-- Statement-only formalization of Thousand Theorems artifact Q1139041
-- (thousand-theorems__lean4__Q1139041), "Cauchy's theorem (group theory)":
-- if a prime divides the order of a finite group, the group has an element of that prime order.
-- This file contains no proof.

module

public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace Q1139041

/-- Cauchy's theorem for finite groups. -/
theorem exists_prime_orderOf_dvd_card_statement {G : Type*} [Group G] [Fintype G] (p : ℕ)
    [Fact p.Prime] (hdvd : p ∣ Fintype.card G) : ∃ x : G, orderOf x = p := sorry

end Q1139041

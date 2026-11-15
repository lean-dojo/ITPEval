-- Statement-only formalization of Thousand Theorems artifact Q1057919
-- (thousand-theorems__lean4__Q1057919), "Sylow theorems": existence of
-- prime-power-order subgroups, conjugacy of Sylow subgroups, and divisibility
-- and congruence properties of their number. This file contains no proof.

module

public import Mathlib.GroupTheory.Sylow

@[expose] public section

universe u

namespace Q1057919

open MulAction

variable {G : Type u} [Group G]
variable {p : ℕ}

/-- If `p ^ n` divides the cardinality of `G`, then `G` has a subgroup of that cardinality. -/
theorem exists_subgroup_card_pow_prime [Finite G] (p : ℕ) {n : ℕ} [Fact p.Prime]
    (hdvd : p ^ n ∣ Nat.card G) : ∃ K : Subgroup G, Nat.card K = p ^ n := sorry

/-- If there are finitely many Sylow `p`-subgroups, any two are conjugate. -/
theorem isPretransitive_of_finite [Fact p.Prime] [Finite (Sylow p G)] :
    IsPretransitive G (Sylow p G) := sorry

/-- The number of Sylow `p`-subgroups divides the index of each Sylow `p`-subgroup. -/
theorem card_dvd_index [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) :
    Nat.card (Sylow p G) ∣ P.index := sorry

/-- The number of Sylow `p`-subgroups is congruent to one modulo `p`. -/
theorem card_sylow_modEq_one (p : ℕ) (G : Type u) [Group G]
    [Fact p.Prime] [Finite (Sylow p G)] :
    Nat.card (Sylow p G) ≡ 1 [MOD p] := sorry

end Q1057919

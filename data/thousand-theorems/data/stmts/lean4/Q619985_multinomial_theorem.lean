-- Statement-only formalization of Thousand Theorems artifact Q619985
-- (thousand-theorems__lean4__Q619985), "Multinomial theorem": for pairwise
-- commuting values indexed by a finite set in a semiring, the power of their
-- sum is the multinomial sum over exponent functions of the same total degree.
-- This file contains no proof.

module

public import Mathlib.Data.Nat.Choose.Multinomial

@[expose] public section

open Finset
open scoped Function

namespace Q619985

variable {α R : Type*} [DecidableEq α] [Semiring R]

/-- The multinomial expansion for a finite family of pairwise commuting semiring elements. -/
theorem sum_pow_eq_sum_piAntidiag_of_commute (s : Finset α) (f : α → R)
    (hc : (s : Set α).Pairwise (Commute on f)) (n : ℕ) :
    (∑ i ∈ s, f i) ^ n =
      ∑ k ∈ piAntidiag s n, Nat.multinomial s k *
        s.noncommProd (fun i ↦ f i ^ k i) (hc.mono' fun _ _ h ↦ h.pow_pow ..) := sorry

end Q619985

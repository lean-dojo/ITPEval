-- Statement-only formalization of Thousand Theorems artifact Q2379132
-- (thousand-theorems__lean4__Q2379132), "Going-up and going-down theorems":
-- the two indexed going-up results, the prime-spectrum characterization of
-- going-down, and the localized-spectrum surjectivity criterion.
-- This file contains no proofs.

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs

@[expose] public section

namespace Q2379132

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

def HasGoingDownStatement : Prop :=
  ∀ p q : Ideal R, p.IsPrime → q.IsPrime → p ≤ q →
    ∀ Q : Ideal S, Q.IsPrime → Q.comap (algebraMap R S) = q →
      ∃ P : Ideal S, P.IsPrime ∧ P ≤ Q ∧ P.comap (algebraMap R S) = p

def PrimeSpectrumComapIsGeneralizingStatement : Prop :=
  ∀ Q : Ideal S, Q.IsPrime →
    ∀ p : Ideal R, p.IsPrime → p ≤ Q.comap (algebraMap R S) →
      ∃ P : Ideal S, P.IsPrime ∧ P ≤ Q ∧ P.comap (algebraMap R S) = p

def LocalPrimeSpectrumComapSurjectiveStatement (Q : Ideal S) : Prop :=
  ∀ p : Ideal R, p.IsPrime → p ≤ Q.comap (algebraMap R S) →
    ∃ P : Ideal S, P.IsPrime ∧ P ≤ Q ∧ P.comap (algebraMap R S) = p

/-- A prime ideal containing the algebra-map kernel has a prime ideal lying over it. -/
theorem exists_ideal_over_prime_of_isIntegral_of_isDomain_statement
    [IsDomain S] [Algebra.IsIntegral R S] (P : Ideal R) [P.IsPrime]
    (hP : RingHom.ker (algebraMap R S) ≤ P) :
    ∃ Q : Ideal S, Q.IsPrime ∧ Q.comap (algebraMap R S) = P := sorry

/-- General going-up above an already chosen prime ideal upstairs. -/
theorem exists_ideal_over_prime_of_isIntegral_of_isPrime_statement
    [Algebra.IsIntegral R S] (P : Ideal R) [P.IsPrime]
    (I : Ideal S) [I.IsPrime] (hIP : I.comap (algebraMap R S) ≤ P) :
    ∃ Q ≥ I, Q.IsPrime ∧ Q.comap (algebraMap R S) = P := sorry

/-- Going-down is exactly generalization lifting along contraction on prime spectra. -/
theorem hasGoingDown_iff_generalizingMap_primeSpectrumComap_statement :
    HasGoingDownStatement (R := R) (S := S) ↔
      PrimeSpectrumComapIsGeneralizingStatement (R := R) (S := S) := sorry

/-- Surjectivity on every pair of local prime spectra implies going-down. -/
theorem hasGoingDown_of_comap_localRingHom_surjective_statement
    (H : ∀ Q : Ideal S, Q.IsPrime →
      LocalPrimeSpectrumComapSurjectiveStatement (R := R) Q) :
    HasGoingDownStatement (R := R) (S := S) := sorry

end Q2379132
